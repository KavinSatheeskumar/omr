/*******************************************************************************
 * Copyright IBM Corp. and others 2000
 *
 * This program and the accompanying materials are made available under
 * the terms of the Eclipse Public License 2.0 which accompanies this
 * distribution and is available at https://www.eclipse.org/legal/epl-2.0/
 * or the Apache License, Version 2.0 which accompanies this distribution
 * and is available at https://www.apache.org/licenses/LICENSE-2.0.
 *
 * This Source Code may also be made available under the following Secondary
 * Licenses when the conditions for such availability set forth in the
 * Eclipse Public License, v. 2.0 are satisfied: GNU General Public License,
 * version 2 with the GNU Classpath Exception [1] and GNU General Public
 * License, version 2 with the OpenJDK Assembly Exception [2].
 *
 * [1] https://www.gnu.org/software/classpath/license.html
 * [2] https://openjdk.org/legal/assembly-exception.html
 *
 * SPDX-License-Identifier: EPL-2.0 OR Apache-2.0 OR GPL-2.0-only WITH Classpath-exception-2.0 OR GPL-2.0-only WITH OpenJDK-assembly-exception-1.0
 *******************************************************************************/

#include <ctype.h>
#include <limits.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "env/FrontEnd.hpp"
#include "compile/Compilation.hpp"
#include "compile/Method.hpp"
#include "compile/ResolvedMethod.hpp"
#include "control/Options.hpp"
#include "control/OptionsUtil.hpp"
#include "control/Options_inlines.hpp"
#include "env/CompilerEnv.hpp"
#include "env/PersistentInfo.hpp"
#include "env/TRMemory.hpp"
#include "env/VerboseLog.hpp"
#include "env/jittypes.h"
#include "infra/Assert.hpp"
#include "optimizer/OptimizationManager.hpp"
#include "optimizer/Optimizations.hpp"
#include "optimizer/Optimizer.hpp"
#include "ras/Debug.hpp"
#include "infra/SimpleRegex.hpp"

#define FILTER_POOL_CHUNK_SIZE 32768

#define FILTER_SIZE (sizeof(TR::CompilationFilters) + sizeof(TR_FilterBST *) * FILTER_HASH_SIZE)


void *TR_FilterBST::operator new(size_t size, TR::PersistentAllocator &allocator) { return allocator.allocate(size); }

TR_FilterBST *TR_FilterBST::find(const char *methodName, int32_t methodNameLen)
{
    // Find the filter for the given method name in the tree rooted at node.
    //
    int32_t rc;
    TR_FilterBST *node;

    for (node = this; node; node = node->getChild(rc)) {
        rc = strncmp(methodName, node->getName(), methodNameLen);
        if (rc == 0) {
            rc = methodNameLen - node->getNameLen();
            if (rc == 0)
                break;
        }
        rc = (rc < 0) ? 0 : 1;
    }
    return node;
}

TR_FilterBST *TR_FilterBST::find(const char *methodName, int32_t methodNameLen, const char *methodClass,
    int32_t methodClassLen, const char *methodSignature, int32_t methodSignatureLen)
{
    // Find the filter for the given method name, class and signature in the
    // tree rooted at node.
    //
    int32_t rc;
    TR_FilterBST *node;

    for (node = this; node; node = node->getChild(rc)) {
        rc = strncmp(methodName, node->getName(), methodNameLen);
        if (rc == 0)
            rc = methodNameLen - node->getNameLen();
        if (rc == 0) {
            rc = strncmp(methodClass, node->getClass(), methodClassLen);
            if (rc == 0)
                rc = methodClassLen - static_cast<int32_t>(strlen(node->getClass()));
            if (rc == 0) {
                rc = strncmp(methodSignature, node->getSignature(), methodSignatureLen);
                if (rc == 0)
                    rc = methodSignatureLen - static_cast<int32_t>(strlen(node->getSignature()));
                if (rc == 0)
                    break;
            }
        }
        rc = (rc < 0) ? 0 : 1;
    }
    return node;
}

TR_FilterBST *TR_FilterBST::findRegex(const char *methodSpec)
{
    TR_FilterBST *f;
    for (f = this; f && !f->_regex->match(methodSpec); f = f->getNext())
        ;
    return f;
}

void TR_FilterBST::insert(TR_FilterBST *node)
{
    // Insert this filter into the tree rooted at node. If the filter already
    // exists, don't insert the new one.
    //
    int32_t rc;

    while (node) {
        rc = strcmp(getName(), node->getName());
        if (rc == 0) {
            rc = strcmp(getClass(), node->getClass());
            if (rc == 0) {
                rc = strcmp(getSignature(), node->getSignature());
                if (rc == 0)
                    break;
            }
        }

        TR_FilterBST *child;
        rc = (rc < 0) ? 0 : 1;
        child = node->getChild(rc);
        if (child)
            node = child;
        else {
            node->setChild(rc, this);
            break;
        }
    }
}

void TR_Debug::print(TR_FilterBST *filter)
{
    TR_VerboseLog::CriticalSection vlogLock;
    /*
    if (filter->_optionSet)
       TR_VerboseLog::write("   {%d}", filter->_optionSet);

    if (filter->_lineNumber)
       TR_VerboseLog::write("   [%d]", filter->_lineNumber);
    */

    switch (filter->_filterType) {
        case TR_FILTER_EXCLUDE_NAME_ONLY:
            TR_VerboseLog::write("   -%s", "NAME_ONLY");
            break;
        case TR_FILTER_EXCLUDE_NAME_AND_SIG:
            TR_VerboseLog::write("   -%s", "NAME_AND_SIG");
            break;
        case TR_FILTER_EXCLUDE_SPECIFIC_METHOD:
            TR_VerboseLog::write("   -%s", "SPECIFIC_METHOD");
            break;
        case TR_FILTER_EXCLUDE_REGEX:
            TR_VerboseLog::write("   -%s", "REGEX");
            break;
        case TR_FILTER_NAME_ONLY:
            TR_VerboseLog::write("   +%s", "NAME_ONLY");
            break;
        case TR_FILTER_NAME_AND_SIG:
            TR_VerboseLog::write("   +%s", "NAME_AND_SIG");
            break;
        case TR_FILTER_SPECIFIC_METHOD:
            TR_VerboseLog::write("   +%s", "SPECIFIC_METHOD");
            break;
        case TR_FILTER_REGEX:
            TR_VerboseLog::write("   +%s", "REGEX");
            break;
    }

    switch (filter->_filterType) {
        case TR_FILTER_EXCLUDE_NAME_ONLY:
            TR_VerboseLog::write("   {^*.%s(*}\n", filter->getName());
            break;
        case TR_FILTER_EXCLUDE_NAME_AND_SIG:
            TR_VerboseLog::write("   {^*.%s%s}\n", filter->getName(), filter->getSignature());
            break;
        case TR_FILTER_EXCLUDE_SPECIFIC_METHOD:
            TR_VerboseLog::write("   {^%s.%s%s}\n", filter->getClass(), filter->getName(), filter->getSignature());
            break;
        case TR_FILTER_EXCLUDE_REGEX:
            TR_VerboseLog::write("  ");
            filter->getRegex()->print(true);
            TR_VerboseLog::write("\n");
            break;
        case TR_FILTER_NAME_ONLY:
            TR_VerboseLog::write("   {*.%s(*}\n", filter->getName());
            break;
        case TR_FILTER_NAME_AND_SIG:
            TR_VerboseLog::write("   {*.%s%s}\n", filter->getName(), filter->getSignature());
            break;
        case TR_FILTER_SPECIFIC_METHOD:
            TR_VerboseLog::write("   {%s.%s%s}\n", filter->getClass(), filter->getName(), filter->getSignature());
            break;
        case TR_FILTER_REGEX:
            TR_VerboseLog::write("  ");
            filter->getRegex()->print(false);
            TR_VerboseLog::write("\n");
            break;
    }

    if (filter->subGroup) {
        TR_VerboseLog::write("   [\n");
        printFilters(filter->subGroup);
        TR_VerboseLog::write("   ]\n");
    }
}

void TR_Debug::printFilters(TR::CompilationFilters *filters)
{
    int32_t i;
    if (filters) {
        if (filters->filterHash) {
            for (i = 0; i < FILTER_HASH_SIZE; i++)
                if (filters->filterHash[i])
                    printFilterTree(filters->filterHash[i]);
        }

        if (filters->filterNameList) {
            printFilterTree(filters->filterNameList);
        }

        if (filters->filterRegexList) {
            for (TR_FilterBST *filter = filters->filterRegexList; filter; filter = filter->getNext())
                print(filter);
        }
    }
}

void TR_Debug::printFilters()
{
    TR_VerboseLog::CriticalSection vlogLock;
    TR_VerboseLog::writeLine("<compilationFilters>");
    printFilters(_compilationFilters);
    TR_VerboseLog::writeLine("</compilationFilters>");

    TR_VerboseLog::writeLine("<relocationFilters>");
    printFilters(_relocationFilters);
    TR_VerboseLog::writeLine("</relocationFilters>");

    TR_VerboseLog::writeLine("<inlineFilters>");
    printFilters(_inlineFilters);
    TR_VerboseLog::writeLine("</inlineFilters>");
}

void TR_Debug::printFilterTree(TR_FilterBST *root)
{
    if (root->getChild(0))
        printFilterTree(root->getChild(0));
    print(root);
    if (root->getChild(1))
        printFilterTree(root->getChild(1));
}

int32_t TR_Debug::scanFilterName(const char *string, TR_FilterBST *filter)
{
    // help for OMR parsing
    bool seenFileName = false;
    bool seenLineNumber = false;
    bool omrPattern = false;

    // Walk the filter to determine the type.
    //
    // TR_VerboseLog::writeLine("filterName: %s", string);
    const char *nameChars = NULL;
    int32_t nameLen = 0;
    const char *classChars = NULL;
    int32_t classLen = 0;
    const char *signatureChars = string;
    int32_t signatureLen = 0;
    char filterType = filter->getFilterType();
    if (*string == '/' || *string == '.') // hack that works for linux
        omrPattern = true;

    while (*string && *string != '\t' && *string != ',' && *string != '\n') {
        if (omrPattern) {
            if (*string == ':') {
                if (!seenFileName) {
                    classChars = signatureChars;
                    classLen = signatureLen;
                    signatureChars = string + 1;
                    signatureLen = 0;
                    seenFileName = true;
                } else if (!seenLineNumber) {
                    nameChars = signatureChars;
                    nameLen = signatureLen;
                    signatureChars = string + 1;
                    signatureLen = 0;
                    seenLineNumber = true;
                }
            } else if (seenLineNumber && *string == ' ') {
                break;
            }

            else
                signatureLen++;
        } else {
            if (*string == ' ')
                break;

            if (*string == '.') {
                classChars = signatureChars;
                classLen = signatureLen;
                signatureChars = string + 1;
                signatureLen = 0;
                filterType = filter->isExclude() ? TR_FILTER_EXCLUDE_SPECIFIC_METHOD : TR_FILTER_SPECIFIC_METHOD;
            }

            else if (*string == '(') {
                nameChars = signatureChars;
                nameLen = signatureLen;
                signatureChars = string;
                signatureLen = 1;
                if (filterType == TR_FILTER_EXCLUDE_NAME_ONLY || filterType == TR_FILTER_NAME_ONLY) {
                    filterType = filter->isExclude() ? TR_FILTER_EXCLUDE_NAME_AND_SIG : TR_FILTER_NAME_AND_SIG;
                }
            } else
                signatureLen++;
        }

        string++;
    }

    if (!nameChars) {
        nameChars = signatureChars;
        nameLen = signatureLen;
        signatureChars = NULL;
        signatureLen = 0;
    }

    // signal for OMR style signature
    if (omrPattern) {
        // need to swap name and signature, since name is currently the line number
        const char *tempChars = nameChars;
        int32_t tempLen = nameLen;
        nameChars = signatureChars;
        nameLen = signatureLen;
        signatureChars = tempChars;
        signatureLen = tempLen;
        filterType = filter->isExclude() ? TR_FILTER_EXCLUDE_SPECIFIC_METHOD : TR_FILTER_SPECIFIC_METHOD;
    }

    // Keep copies of the method name, class, and signature, and point
    // the filter members to them
    //
    int32_t length = nameLen + classLen + signatureLen;
    char *buf = (char *)(TR::Compiler->regionAllocator.allocate(length + 3)); // NULL terminated strings

    filter->setName(buf, nameLen);
    if (nameChars) {
        strncpy(buf, nameChars, nameLen);
        buf += nameLen;
    }
    *(buf++) = 0;
    filter->setClass(buf);
    if (classChars) {
        strncpy(buf, classChars, classLen);
        buf += classLen;
    }
    *(buf++) = 0;
    filter->setSignature(buf);
    if (signatureChars) {
        strncpy(buf, signatureChars, signatureLen);
        buf += signatureLen;
    }
    *(buf++) = 0;

    filter->setFilterType(filterType);
    return length;
}

int32_t *TR_Debug::loadCustomStrategy(char *fileName)
{
    TR_VerboseLog::CriticalSection vlogLock;
    int32_t *customStrategy = NULL;
    FILE *optFile = fopen(fileName, "r");
    if (optFile) {
        char lineBuffer[1000];
        int32_t optNumBuffer[1000];
        int32_t optCount = 0;

        while (fgets(lineBuffer, sizeof(lineBuffer), optFile)) {
            if (optCount >= (sizeof(optNumBuffer) / sizeof(optNumBuffer[0]))) {
                TR_VerboseLog::writeLine(TR_Vlog_INFO, "Reached limit of %d optFile lines; ignoring subsequent lines",
                    optCount);
                break;
            }

            int optIndex;
            if (!sscanf(lineBuffer, "Performing %d: ", &optIndex))
                continue;

            char *name = strchr(lineBuffer, ':') + 2; // 2 moves past the colon and the space
            int32_t nameLen = static_cast<int32_t>(strcspn(name, " \n"));

            int32_t optNum;
            for (optNum = 0; optNum < OMR::numOpts; optNum++) {
                const char *actualName = OMR::Optimizer::getOptimizationName((OMR::Optimizations)optNum);
                if (!strncmp(name, actualName, nameLen)) {
                    int32_t flags = 0;
                    if (strstr(name + nameLen, "mustBeDone"))
                        flags |= TR::Options::MustBeDone;
                    optNumBuffer[optCount++] = optNum | flags;
                    break;
                }
            }
            if (optNum == OMR::numOpts)
                TR_VerboseLog::writeLine(TR_Vlog_INFO, "Ignoring optFile line; no matching opt name for '%s'", name);
        }

        if (optCount > 0) {
            int32_t srcSize = optCount * sizeof(optNumBuffer[0]);
            customStrategy = (int32_t *)(TR::Compiler->regionAllocator.allocate(
                srcSize + sizeof(optNumBuffer[0]))); // One extra for the endOpts entry
            memcpy(customStrategy, optNumBuffer, srcSize);
            customStrategy[optCount] = OMR::endOpts;
        } else {
            TR_VerboseLog::writeLine(TR_Vlog_INFO, "Ignoring optFile; contains no suitable opt names");
        }
    } else {
        TR_VerboseLog::writeLine(TR_Vlog_INFO, "optFile not found: '%s'", fileName);
    }
    return customStrategy;
}
