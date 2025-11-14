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

// -----------------------------------------------------------------------------
// TR::CompilationFilters
// -----------------------------------------------------------------------------

void TR::CompilationFilters::clear()
{
    char *buf = (char *)this;
    int32_t size = FILTER_SIZE;
    memset(buf, 0, size);

    filterHash = (TR_FilterBST **)(buf + sizeof(TR::CompilationFilters));
    setDefaultExclude(false);
    excludedMethodFilter = NULL;
}

TR::CompilationFilters *TR::CompilationFilters::build()
{
    int32_t size = sizeof(TR::CompilationFilters) + sizeof(TR_FilterBST *) * FILTER_HASH_SIZE;

    char *buf = (char *)(TR::Compiler->regionAllocator.allocate(size));

    TR::CompilationFilters *filters = (TR::CompilationFilters *)buf;
    filters->clear();
    return filters;
}

TR_FilterBST *TR::CompilationFilters::addFilter(const char *&filterString, bool scanningExclude, int32_t optionSetIndex,
    int32_t lineNum)
{
    uint32_t filterType = scanningExclude ? TR_FILTER_EXCLUDE_NAME_ONLY : TR_FILTER_NAME_ONLY;

    TR_FilterBST *filterBST = new (TR::Compiler->regionAllocator) TR_FilterBST(filterType, optionSetIndex, lineNum);

    int32_t nameLength;
    if (*filterString == '{') {
        const char *filterCursor = filterString;
        filterType = scanningExclude ? TR_FILTER_EXCLUDE_REGEX : TR_FILTER_REGEX;
        filterBST->setFilterType(filterType);

        // Create the regular expression from the regex string
        //
        TR::SimpleRegex *regex = TR::SimpleRegex::create(filterCursor);
        if (!regex) {
            fprintf(stderr, "FAILURE: Bad regular expression at --> '%s'\n", filterCursor);
            return 0;
        }
        nameLength = static_cast<int32_t>(filterCursor - filterString);
        filterBST->setRegex(regex);
        filterBST->setNext(hasRegexFilter() ? filterRegexList : NULL);
        filterRegexList = filterBST;
        setHasRegexFilter();
    } else {
        // Note - the following call changes the filterType field in the filterBST
        //
        nameLength = filterBST->scanFilterName(filterString);
        if (!nameLength)
            return 0;

        // Add the filter to the appropriate data structure
        //
        filterType = filterBST->getFilterType();
        if (filterType == TR_FILTER_EXCLUDE_NAME_ONLY || filterType == TR_FILTER_NAME_ONLY) {
            if (filterNameList)
                filterBST->insert(filterNameList);
            else
                filterNameList = filterBST;
            setHasNameFilter();
        } else {
            TR_FilterBST **bucket = &(filterHash[nameLength % FILTER_HASH_SIZE]);

            if (*bucket)
                filterBST->insert(*bucket);
            else
                *bucket = filterBST;

            if (filterType == TR_FILTER_NAME_AND_SIG || filterType == TR_FILTER_EXCLUDE_NAME_AND_SIG)
                setHasNameSigFilter();
            else
                setHasClassNameSigFilter();
        }
    }

    // We start by assuming we are including everything by default.
    // If we find a +ve filter (i.e. include only this) which is not part of an
    // option subset, change the default to be exclude everything.
    //
    if (!scanningExclude && optionSetIndex == 0) {
        setDefaultExclude(true);
    }

    filterString += nameLength;
    return filterBST;
}

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


const char *TR::CompilationFilters::limitOption(const char *option, void *base, TR::OptionTable *entry,
    TR::Options *cmdLineOptions)
{
    const char *p = option;

    TR_FilterBST *filter = addFilter(p, entry->parm1, 0, 0);

    if (!filter)
        return option;

    int32_t len = static_cast<int32_t>(p - option);
    char *limitName = (char *)(TR::Compiler->regionAllocator.allocate(len + 1));
    memcpy(limitName, option, len);
    limitName[len] = 0;
    entry->msgInfo = (intptr_t)limitName;

    // Look for option subset if this is "limit" rather than "exclude"
    //
    TR::SimpleRegex *methodRegex = filter->getRegex();
    if (methodRegex && !entry->parm1 && (*p == '(' || *p == '{')) {
        TR::SimpleRegex *optLevelRegex = NULL;

        // Scan off the opt level regex if it is present
        //
        if (*p == '{') {
            optLevelRegex = TR::SimpleRegex::create(p);
            if (!optLevelRegex || *p != '(') {
                if (!optLevelRegex) {
                    TR_VerboseLog::writeLineLocked(TR_Vlog_FAILURE, "Bad regular expression at --> '%s'", p);
                }
                return option;
            }
        }
        // If an option subset was found, save the information for later
        // processing
        //
        const char *startOptString = ++p;
        int32_t parenNest = 1;
        for (; *p; p++) {
            if (*p == '(')
                parenNest++;
            else if (*p == ')') {
                if (--parenNest == 0) {
                    p++;
                    break;
                }
            }
        }
        if (parenNest)
            return startOptString;

        // Save the option set - its option string will be processed after
        // the main options have been finished.
        //
        TR::OptionSet *newSet = (TR::OptionSet *)(TR::Compiler->regionAllocator.allocate(sizeof(TR::OptionSet)));
        newSet->init(startOptString);
        newSet->setMethodRegex(methodRegex);
        newSet->setOptLevelRegex(optLevelRegex);
        cmdLineOptions->saveOptionSet(newSet);
    }

    return p;
}

bool TR::CompilationFilters::methodSigCanBeFound(const char *methodSig, TR::Method::Type methodType,
    TR_FilterBST *&filter)
{
    const char *methodClass, *methodName, *methodSignature;
    uint32_t methodClassLen, methodNameLen, methodSignatureLen;

    methodClass = methodSig;
    if (methodType != TR::Method::J9) {
        if (methodSig[0] == '/' || methodSig[0] == '.') // omr method pattern
        {
            methodClass = methodSig;
            methodSignature = strchr(methodSig, ':');
            methodClassLen = static_cast<uint32_t>(methodSignature - methodClass);
            methodSignature++;
            methodName = strchr(methodSignature, ':');
            methodSignatureLen = static_cast<uint32_t>(methodName - methodSignature);
            methodName++;
            methodNameLen = static_cast<uint32_t>(strlen(methodName));
        } else {
            methodName = methodSig;
            methodClassLen = 0;
            methodSignature = "";
            methodSignatureLen = 0;
            methodNameLen = static_cast<uint32_t>(strlen(methodName));
        }
    } else {
        if (methodSig[0] == '/') // omr method pattern
        {
            methodClass = methodSig;
            methodSignature = strchr(methodSig, ':');
            methodClassLen = static_cast<uint32_t>(methodSignature - methodClass);
            methodSignature++;
            methodName = strchr(methodSignature, ':');
            methodSignatureLen = static_cast<uint32_t>(methodName - methodSignature);
            methodName++;
            methodNameLen = static_cast<uint32_t>(strlen(methodName));
        } else {
            methodName = strchr(methodSig, '.');
            methodClassLen = static_cast<uint32_t>(methodName - methodClass);
            methodName++;
            methodSignature = strchr(methodName, '(');
            methodSignatureLen = static_cast<uint32_t>(strlen(methodSignature));
            TR_ASSERT(methodSignature, "unable to pattern match java method signature");
            methodNameLen = static_cast<uint32_t>(methodSignature - methodName);
        }
    }

    int32_t length = methodNameLen + methodSignatureLen;

    if (hasClassNameSigFilter() || hasNameSigFilter()) {
        if (hasClassNameSigFilter()) {
            // Search for the class+name+signature.
            //
            filter = filterHash[(length + methodClassLen) % FILTER_HASH_SIZE];
            if (filter)
                filter = filter->find(methodName, methodNameLen, methodClass, methodClassLen, methodSignature,
                    methodSignatureLen);
        }

        if (!filter && hasNameSigFilter()) {
            // Search for the name+signature.
            //
            filter = filterHash[length % FILTER_HASH_SIZE];
            if (filter)
                filter = filter->find(methodName, methodNameLen, "", 0, methodSignature, methodSignatureLen);
        }
    }

    if (!filter && hasNameFilter()) {
        // Search the name filter list.
        //
        filter = filterNameList;
        if (filter)
            filter = filter->find(methodName, methodNameLen);
    }

    if (!filter && hasRegexFilter()) {
        // Search the regex filter list.
        //
        filter = filterRegexList;
        if (filter)
            filter = filter->findRegex(methodSig);
    }

    bool excluded = defaultExclude() != 0;
    if (filter) {
        switch (filter->getFilterType()) {
            case TR_FILTER_EXCLUDE_NAME_ONLY:
            case TR_FILTER_EXCLUDE_NAME_AND_SIG:
            case TR_FILTER_EXCLUDE_SPECIFIC_METHOD:
            case TR_FILTER_EXCLUDE_REGEX:
                excluded = true;
                break;
            default:
                excluded = false;
                break;
        }
    }

    return !excluded;
}

bool TR::CompilationFilters::methodCanBeFound(TR_Memory *trMemory, TR_ResolvedMethod *method, TR_FilterBST *&filter)
{
    const char *methodSig = method->signature(trMemory);
    return methodSigCanBeFound(methodSig, method->convertToMethod()->methodType(), filter);
}


bool TR::CompilationFilters::scanInlineFilters(::FILE *inlineFile, int32_t &lineNumber)
{
    char limitReadBuffer[1024];
    bool inlineFileError = false;
    TR_FilterBST *filter = NULL;

    while (fgets(limitReadBuffer, sizeof(limitReadBuffer), inlineFile)) {
        ++lineNumber;
        // ignore range for now
        // if (lineNumber < firstLine || lineNumber > lastLine)
        //    continue;

        char includeFlag = limitReadBuffer[0];

        if (includeFlag == '[') {
            // TR_VerboseLog::writeLine(TR_Vlog_INFO, "Sub inline file entry start --> '%s'", limitReadBuffer);

            if (filter) {
                filter->subGroup = TR::CompilationFilters::build();
                filter->subGroup->setDefaultExclude(true);
                inlineFileError = !filter->subGroup->scanInlineFilters(inlineFile, lineNumber);
            }

        } else if (includeFlag == ']') {
            // TR_VerboseLog::writeLine(TR_Vlog_INFO, "Sub inline file entry end --> '%s'", limitReadBuffer);
            //  always return true (success)
            //  this will ignore the rest of the filters if no matching open bracket.
            return true;
        } else if (includeFlag == '+' || includeFlag == '-') {
            const char *p = limitReadBuffer + 1;
            int32_t optionSet;
            if (*p >= '0' && *p <= '9')
                optionSet = *(p++) - '0';
            else
                optionSet = 0;
            if (*(p++) != ' ') {
                inlineFileError = true;
                break;
            }
            // Skip hotness level if it is present
            //
            if (*p == '(') {
                for (p++; *p && *p != ')'; p++) {
                }
                if (*(p++) != ')') {
                    inlineFileError = true;
                    break;
                }
                if (*(p++) != ' ') {
                    inlineFileError = true;
                    break;
                }
            }

            filter = this->addFilter(p, (('+' == includeFlag) ? 0 : 1), optionSet, lineNumber);

            if (!filter) {
                inlineFileError = true;
                TR_VerboseLog::writeLineLocked(TR_Vlog_FAILURE, "Bad inline file entry --> '%s'", limitReadBuffer);
                break;
            }
        }
    }

    return !inlineFileError;
}

/** \brief
 *     This function opens the inlinefile and adds its entries to a TR::CompilationFilters.
 *
 *     An inlinefile is a file containing a list of methods, one per line, which the inliner will limit itself to
 *     when trying to perform inlining. In other words, only methods from the file can be inlined, but there is no
 *     guarantee that any of them will be inlined. The format for entry is:
 *
 *     + signature
 *
 *  \param option
 *     Points to the first char after inlinefile=
 *
 *  \param base
 *     Unused variable needed for downstream projects.
 *
 *  \param entry
 *     The option table entry for this option.
 *
 *  \param cmdLineOptions
 *     Unused variable needed for downstream projects.
 *
 *  \return
 *     The unmodified parameter option if there is a problem with the file, aborting JIT initialization.
 *     Otherwise a pointer to the next comma or NULL.
 */
const char *TR::CompilationFilters::inlinefileOption(const char *option, void *base, TR::OptionTable *entry,
    TR::Options *cmdLineOptions)
{
    const char *endOpt = option;
    const char *name = option;
    const char *fail = option;

    // move to the end of this option
    for (; *endOpt && *endOpt != ','; endOpt++) {
    }

    int32_t len = static_cast<int32_t>(endOpt - name);
    if (!len)
        return option;

    char *inlineFileName = (char *)(TR::Compiler->regionAllocator.allocate(len + 1));
    memcpy(inlineFileName, name, len);
    inlineFileName[len] = 0; // NULL terminate the copied string
    entry->msgInfo = (intptr_t)inlineFileName;

    ::FILE *inlineFile = fopen(inlineFileName, "r");
    bool success = false;

    if (inlineFile) {
        // initializing _inlineFilters using the new interface

        this->setDefaultExclude(true);

        int32_t lineNumber = 0;

        success = this->scanInlineFilters(inlineFile, lineNumber);

        fclose(inlineFile);
    }

    if (!success) {
        TR_VerboseLog::writeLineLocked(TR_Vlog_FAILURE, "Unable to read inline file --> '%s'", inlineFileName);
        return fail; // We want to fail if we can't read the file because it is too easy to miss that the file wasn't
                     // picked up
    }
    return endOpt;
}

/** \brief
 *     Processes a limitfile= option, parses and applies the limitfile to compilation control.
 *
 *     A limitfile is a compiler verbose log, produced by the option -Xjit:verbose,vlog=filename
 *     When a verbose log is used as a limitfile, only the methods contained within the file
 *     will be compiled if they are queued for compilation. The format of the method entries in
 *     the file must match that of a verbose log.
 *
 *     The option can be used in 2 ways:
 *     limitfile=filename
 *     limitfile=(filename,xx,yy)
 *
 *     The when the latter is used, xx-yy denotes a line number range (starting at zero and ignoring # comments)
 *     to restrict the limiting to. This is commonly used in debugging to narrow down a problem to a specific
 *     method by doing a binary search on the limitfile.
 *
 *  \param option
 *     Points to the first char after inlinefile=
 *
 *  \param base
 *     Unused variable needed for downstream projects.
 *
 *  \param entry
 *     The option table entry for this option.
 *
 *  \param cmdLineOptions
 *     The command line options.
 *
 *  \param loadLimit
 *     The load limit.
 *
 *  \param pseudoRandomListHeadPtr
 *     A list of pseudo random numbers.
 *
 *  \return
 *     The unmodified parameter option if there is a problem with the file, aborting JIT initialization.
 *     Otherwise a pointer to the next comma or NULL.
 */
#define PSEUDO_RANDOM_NUMBER_PREFIX "#num"
#define PSEUDO_RANDOM_NUMBER_PREFIX_LEN 4
#define PSEUDO_RANDOM_SUFFIX '#'
const char *TR::CompilationFilters::limitfileOption(const char *option, void *base, TR::OptionTable *entry,
    TR::Options *cmdLineOptions, TR_PseudoRandomNumbersListElement **pseudoRandomListHeadPtr)
{
    const char *endOpt = option;
    const char *name = option;
    const char *fail = option;

    bool range = false;
    if (*endOpt == '(') {
        ++endOpt;
        ++name;
        range = true;
    }

    for (; *endOpt && *endOpt != ','; endOpt++) {
    }
    int32_t len = static_cast<int32_t>(endOpt - name);
    if (!len)
        return option;

    char *limitFileName = (char *)(TR::Compiler->regionAllocator.allocate(len + 1));
    memcpy(limitFileName, name, len);
    limitFileName[len] = 0;
    entry->msgInfo = (intptr_t)limitFileName;

    intptr_t firstLine = 1, lastLine = INT_MAX;
    if (range) {
        if (!*endOpt)
            return option;
        firstLine = TR::Options::getNumericValue(++endOpt);
        if (*endOpt == ',')
            lastLine = TR::Options::getNumericValue(++endOpt);
        if (*endOpt != ')')
            return option;
        ++endOpt;
    }

    ::FILE *limitFile = fopen(limitFileName, "r");
    if (limitFile) {
        this->setDefaultExclude(true);

        char limitReadBuffer[1024];
        bool limitFileError = false;
        int32_t lineNumber = 0;

        TR_PseudoRandomNumbersListElement *pseudoRandomListHead = NULL;
        if (pseudoRandomListHeadPtr)
            pseudoRandomListHead = *pseudoRandomListHeadPtr;
        TR_PseudoRandomNumbersListElement *curPseudoRandomListElem = pseudoRandomListHead;
        int32_t curIndex = 0;

        while (fgets(limitReadBuffer, sizeof(limitReadBuffer), limitFile)) {
            ++lineNumber;
            if (lineNumber < firstLine || lineNumber > lastLine)
                continue;

            char includeFlag = limitReadBuffer[0];
            if (strncmp(limitReadBuffer, "-precompileMethod", 17) == 0) {
                const char *p = limitReadBuffer + 18;
                if (!this->addFilter(p, 0, 0, lineNumber)) {
                    limitFileError = true;
                    break;
                }
            } else if (strncmp(limitReadBuffer, "-noprecompileMethod", 19) == 0) {
                const char *p = limitReadBuffer + 20;
                if (!this->addFilter(p, 1, 0, lineNumber)) {
                    limitFileError = true;
                    break;
                }
            } else if (includeFlag == '+' || includeFlag == '-') {
                const char *p = limitReadBuffer + 1;
                int32_t optionSet;
                if (*p >= '0' && *p <= '9')
                    optionSet = *(p++) - '0';
                else
                    optionSet = 0;
                if (*(p++) != ' ') {
                    limitFileError = true;
                    break;
                }
                // Skip hotness level if it is present
                //
                if (*p == '(') {
                    for (p++; *p && *p != ')'; p++) {
                    }
                    if (*(p++) != ')') {
                        limitFileError = true;
                        break;
                    }
                    if (*(p++) != ' ') {
                        limitFileError = true;
                        break;
                    }
                }

                // if (optionSet > 0)
                //    filters->setDefaultExclude(false);

                if (!this->addFilter(p, (('+' == includeFlag) ? 0 : 1), optionSet, lineNumber)) {
                    limitFileError = true;
                    break;
                }
            } else if (strncmp(limitReadBuffer, PSEUDO_RANDOM_NUMBER_PREFIX, PSEUDO_RANDOM_NUMBER_PREFIX_LEN) == 0) {
                char *p = limitReadBuffer + PSEUDO_RANDOM_NUMBER_PREFIX_LEN;

                if (*(p++) != ' ') {
                    limitFileError = true;
                    break;
                }

                bool isNegative = false;
                if (*(p) == '-') {
                    p++;
                    isNegative = true;
                }

                int32_t randNum;
                while (OMR_ISDIGIT(p[0])) {
                    randNum = atoi(p);
                    while (OMR_ISDIGIT(p[0]))
                        ++p;

                    if (isNegative)
                        randNum = -1 * randNum;

                    if ((curPseudoRandomListElem == NULL) || (curIndex == PSEUDO_RANDOM_NUMBERS_SIZE)) {
                        int32_t sz = sizeof(TR_PseudoRandomNumbersListElement);
                        TR_PseudoRandomNumbersListElement *newPseudoRandomListElem
                            = (TR_PseudoRandomNumbersListElement *)(TR::Compiler->regionAllocator.allocate(sz));
                        newPseudoRandomListElem->_next = NULL;
                        curIndex = 0;

                        if (curPseudoRandomListElem == NULL)
                            *pseudoRandomListHeadPtr = newPseudoRandomListElem;
                        else
                            curPseudoRandomListElem->_next = newPseudoRandomListElem;

                        curPseudoRandomListElem = newPseudoRandomListElem;
                    }

                    if (curPseudoRandomListElem == NULL) {
                        limitFileError = true;
                        break;
                    }

                    curPseudoRandomListElem->_pseudoRandomNumbers[curIndex++] = randNum;
                    curPseudoRandomListElem->_curIndex = curIndex;

                    if (*p == PSEUDO_RANDOM_SUFFIX)
                        break;

                    if (*(p++) != ' ') {
                        limitFileError = true;
                        break;
                    }

                    isNegative = false;
                    if (*(p) == '-') {
                        p++;
                        isNegative = true;
                    }
                }
            }
        }
        if (limitFileError) {
            TR_VerboseLog::writeLineLocked(TR_Vlog_FAILURE, "Bad limit file entry --> '%s'", limitReadBuffer);
            return fail;
        }
        fclose(limitFile);
    } else {
        TR_VerboseLog::writeLineLocked(TR_Vlog_FAILURE, "Unable to read limit file --> '%s'", limitFileName);
        return fail; // We want to fail if we can't read the file because it is too easy to miss that the file wasn't
                     // picked up
    }
    return endOpt;
}

//
//TR FilterBST
//

int32_t TR_FilterBST::scanFilterName(const char *string)
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
    char filterType = getFilterType();
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
                filterType = isExclude() ? TR_FILTER_EXCLUDE_SPECIFIC_METHOD : TR_FILTER_SPECIFIC_METHOD;
            }

            else if (*string == '(') {
                nameChars = signatureChars;
                nameLen = signatureLen;
                signatureChars = string;
                signatureLen = 1;
                if (filterType == TR_FILTER_EXCLUDE_NAME_ONLY || filterType == TR_FILTER_NAME_ONLY) {
                    filterType = isExclude() ? TR_FILTER_EXCLUDE_NAME_AND_SIG : TR_FILTER_NAME_AND_SIG;
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
        filterType = isExclude() ? TR_FILTER_EXCLUDE_SPECIFIC_METHOD : TR_FILTER_SPECIFIC_METHOD;
    }

    // Keep copies of the method name, class, and signature, and point
    // the filter members to them
    //
    int32_t length = nameLen + classLen + signatureLen;
    char *buf = (char *)(TR::Compiler->regionAllocator.allocate(length + 3)); // NULL terminated strings

    setName(buf, nameLen);
    if (nameChars) {
        strncpy(buf, nameChars, nameLen);
        buf += nameLen;
    }
    *(buf++) = 0;
    setClass(buf);
    if (classChars) {
        strncpy(buf, classChars, classLen);
        buf += classLen;
    }
    *(buf++) = 0;
    setSignature(buf);
    if (signatureChars) {
        strncpy(buf, signatureChars, signatureLen);
        buf += signatureLen;
    }
    *(buf++) = 0;

    setFilterType(filterType);
    return length;
}

void TR_FilterBST::print()
{
    TR_VerboseLog::CriticalSection vlogLock;
    /*
    if (filter->_optionSet)
       TR_VerboseLog::write("   {%d}", filter->_optionSet);

    if (filter->_lineNumber)
       TR_VerboseLog::write("   [%d]", filter->_lineNumber);
    */

    switch (_filterType) {
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

    switch (_filterType) {
        case TR_FILTER_EXCLUDE_NAME_ONLY:
            TR_VerboseLog::write("   {^*.%s(*}\n", getName());
            break;
        case TR_FILTER_EXCLUDE_NAME_AND_SIG:
            TR_VerboseLog::write("   {^*.%s%s}\n", getName(), getSignature());
            break;
        case TR_FILTER_EXCLUDE_SPECIFIC_METHOD:
            TR_VerboseLog::write("   {^%s.%s%s}\n", getClass(), getName(), getSignature());
            break;
        case TR_FILTER_EXCLUDE_REGEX:
            TR_VerboseLog::write("  ");
            getRegex()->print(true);
            TR_VerboseLog::write("\n");
            break;
        case TR_FILTER_NAME_ONLY:
            TR_VerboseLog::write("   {*.%s(*}\n", getName());
            break;
        case TR_FILTER_NAME_AND_SIG:
            TR_VerboseLog::write("   {*.%s%s}\n", getName(), getSignature());
            break;
        case TR_FILTER_SPECIFIC_METHOD:
            TR_VerboseLog::write("   {%s.%s%s}\n", getClass(), getName(), getSignature());
            break;
        case TR_FILTER_REGEX:
            TR_VerboseLog::write("  ");
            getRegex()->print(false);
            TR_VerboseLog::write("\n");
            break;
    }

    if (subGroup) {
        TR_VerboseLog::write("   [\n");
        subGroup->printFilters();
        TR_VerboseLog::write("   ]\n");
    }
}

