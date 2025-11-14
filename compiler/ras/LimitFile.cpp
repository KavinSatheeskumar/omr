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
#include "control/OMROptions.hpp"
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

void TR::CompilationFilters::printFilters()
{
    int32_t i;
    if (filterHash) {
        for (i = 0; i < FILTER_HASH_SIZE; i++)
            if (filterHash[i])
                filterHash[i]->printFilterTree();
    }

    if (filterNameList) {
        filterNameList->printFilterTree();
    }

    if (filterRegexList) {
        for (TR_FilterBST *filter = filterRegexList; filter; filter = filter->getNext())
            filter->print();
    }
}

void TR_Debug::printFilters()
{
    TR_VerboseLog::CriticalSection vlogLock;
    TR_VerboseLog::writeLine("<compilationFilters>");
    OMR::Options::getCompilationFilters()->printFilters();
    TR_VerboseLog::writeLine("</compilationFilters>");

    TR_VerboseLog::writeLine("<relocationFilters>");
    OMR::Options::getRelocationFilters()->printFilters();
    TR_VerboseLog::writeLine("</relocationFilters>");

    TR_VerboseLog::writeLine("<inlineFilters>");
    OMR::Options::getInlineFilters()->printFilters();
    TR_VerboseLog::writeLine("</inlineFilters>");
}

void TR_FilterBST::printFilterTree()
{
    if (getChild(0))
        getChild(0)->printFilterTree();
    print();
    if (getChild(1))
        getChild(1)->printFilterTree();
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
