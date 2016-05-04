#!/usr/bin/env python

from fields import OFPFC_ADD, OFPFC_DELETE_STRICT, HeaderField
from log import logger

class ForwardingLink(object):
    def __init__(self, rule, isGateway=False):
        self.rule = rule
        self.isGateway = isGateway

    def __eq__(self, other):
        if isinstance(other, self.__class__):
            return self.rule == other.rule and self.isGateway == other.isGateway
        else:
            return False

    def __repr__(self):
        return str(self)

    def __str__(self):
        return "{0} {1}".format(self.rule.location,
                                self.rule.nextHop)

class ForwardingGraph(object):
    def __init__(self):
        self.links = {}
        self.totalRuleCount = 0

    def removeLink(self, rule):
        if rule.location in self.links:
            for link in self.links[rule.location]:
                if link.rule == rule:
                    self.links[rule.location].remove(link)
                    self.totalRuleCount -= 1

    def addLink(self, link):
        if link.rule.location not in self.links:
            self.links[link.rule.location] = []

        self.links[link.rule.location].append(link)
        self.totalRuleCount += 1

    def compare(self, first, second):
        return first.rule.priority >= second.rule.priority

    def __repr__(self):
        return str(self)

    def __str__(self):
        s = "ForwardingGraph - Link count: " + str(self.totalRuleCount)
        for link, rules in self.links.iteritems():
            s += str(link)
            s += "   " + " ".join(str(s) for s in rules)
            s += "\n"
        return s


class EquivalenceRange(object):
    def __init__(self, lowerBound = 0, upperBound = 0):
        self.lowerBound = lowerBound
        self.upperBound = upperBound

    def copy(self):
        return EquivalenceRange(self.lowerBound, self.upperBound)

    def __repr__(self):
        return str(self)

    def __str__(self):
        return "[{0},{1}]".format(self.lowerBound, self.upperBound)

class EquivalenceClass(object):
    def __init__(self, lowerBound = None, upperBound = None):

        if lowerBound is None:
            lowerBound = [0] * HeaderField.End
        if upperBound is None:
            upperBound = [0] * HeaderField.End

        assert len(lowerBound) == len(upperBound)
        for i in range(len(lowerBound)):
            assert lowerBound[i] <= upperBound[i]

        self.lowerBound = list(lowerBound)
        self.upperBound = list(upperBound)

    def getRange(self, findex):
        assert findex <= len(self.lowerBound)
        return self.upperBound[findex] - self.lowerBound[findex]

    def __eq__(self, other):
        if isinstance(other, self.__class__):
            for i in range(len(self.lowerBound)):
                if self.lowerBound[i] != other.lowerBound[i] or \
                   self.upperBound[i] != other.upperBound[i]:
                    return False
            return True
        else:
            return False

    def __repr__(self):
        return str(self)

    def __str__(self):
        # TODO: convert macs, ip values
        return "[{0},{1}]".format(self.lowerBound, self.upperBound)

class Rule(object):
    INVALID_PRIORITY = 0
    DUMMY = 1
    FORWARDING = 2

    def __init__(self):
        self.fieldValue = [0] * HeaderField.End
        self.fieldMask = [0] * HeaderField.End
        self.ruleType = Rule.DUMMY
        self.priority = Rule.INVALID_PRIORITY
        self.wildcards = 0
        self.location = None
        self.nextHop = None

    def getEquivalenceClass(self):
        lb = [0] * HeaderField.End
        ub = [0] * HeaderField.End

        for fname, findex in HeaderField.Index.iteritems():
            fieldValue = 0
            fieldMask = 0

            fieldValue = HeaderField.intValue(findex, self.fieldValue[findex])
            fieldMask = HeaderField.intValue(findex, self.fieldMask[findex])
            maskedValue = fieldValue & fieldMask

            for j in range(HeaderField.Width[findex]):
                lb[findex] <<= 1
                ub[findex] <<= 1

                width = HeaderField.Width[findex]
                maskBit = 1 << ((width - 1) - j)

                if (fieldMask & maskBit) == 0: # wildcard bit
                    ub[findex] |= 1
                else:
                    if (maskedValue & maskBit) == 0: # zero bit
                        pass
                    else: # one bit
                        lb[findex] |= 1
                        ub[findex] |= 1

        return EquivalenceClass(lb, ub)

    def getEquivalenceRange(self, fname):
        findex = HeaderField.Index[fname]
        eqrange = EquivalenceRange()

        fieldValue = 0
        fieldMask = 0

        fieldValue = HeaderField.intValue(findex, self.fieldValue[findex])

        if findex in self.fieldMask:
            fieldMask = HeaderValue.intValue(findex, self.fieldMask[findex])
        else:
            fieldMask = HeaderValue.intValue(findex, self.fieldValue[findex])

        maskedValue = fieldValue & fieldMask

        for j in range(HeaderField.Width[fname]):
            eqrange.lowerBound <<= 1
            eqrange.upperBound <<= 1

            maskBit = 1 << ((HeaderField.Width[fname] - 1) - j)
            if (fieldMask & maskBit) == 0: # wildcard bit
                eqrange.upperBound |= 1
            else:
                if (maskedValue & maskBit) == 0: # zero bit
                    pass
                else: # one bit
                    eqrange.lowerBound |= 1
                    eqrange.upperBound |= 1

        return eqrange

    def __eq__(self, other):
        if isinstance(other, self.__class__):
            if self.location != other.location or \
               self.wildcards != other.wildcards or self.priority != other.priority:
                return False
            for i in range(HeaderField.End):
                if self.fieldValue[i] != other.fieldValue[i] or \
                   self.fieldMask[i] != other.fieldMask[i]:
                    return False
            return True
        else:
            return False

    def __repr__(self):
        return str(self)

    def __str__(self):
        # TODO: convert values
        return "Value: {0}, Mask: {1}, Loc: {2}, NH: {3}, Pri: {4}".format(
            self.fieldValue, self.fieldMask, self.location, self.nextHop, self.priority)

class TrieNode(object):
    def __init__(self):
        self.parent = None
        self.zeroBranch = None
        self.oneBranch = None
        self.wildcardBranch = None
        self.nextLevelTrie = None
        self.ruleSet = None

class Trie(object):
    def __init__(self, fieldIndex):
        self.root = None
        self.fieldName = HeaderField.Index[fieldIndex]
        self.fieldIndex = fieldIndex
        self.totalRuleCount = 0

    def findNode(self, fieldValue, fieldMask):
        if self.root is None or self.totalRuleCount == 0:
            return None

        fieldInt = HeaderField.intValue(self.fieldIndex, fieldValue)
        maskInt = HeaderField.intValue(self.fieldIndex, fieldMask)
        maskedValue = fieldInt & maskInt

        width = HeaderField.Width[self.fieldIndex]
        curnode = self.root

        for i in range(width):
            mask = 1 << ((width - 1) - i)
            if (maskInt & mask) == 0:  # wildcard bit
                if curnode.wildcardBranch is None:
                    return None
                else:
                    curnode = curnode.wildcardBranch
            else:
                if (maskedValue & mask) == 0:  # zero bit
                    if curnode.zeroBranch is None:
                        return None
                    else:
                        curnode = curnode.zeroBranch
                else: # one bit
                    if curnode.oneBranch is None:
                        return None
                    else:
                        curnode = curnode.oneBranch

        return curnode

    # XXX: not incrementing totalRuleCount?
    def addRule(self, rule):
        if self.root is None:
            self.root = TrieNode()

        fieldInt = HeaderField.intValue(self.fieldIndex, rule.fieldValue[self.fieldIndex])
        maskInt = HeaderField.intValue(self.fieldIndex, rule.fieldMask[self.fieldIndex])
        maskedValue = fieldInt & maskInt

        width = HeaderField.Width[self.fieldIndex]
        curnode = self.root

        for i in range(width):
            mask = 1 << ((width - 1) - i)
            if (maskInt & mask) == 0:  # wildcard bit
                if curnode.wildcardBranch is None:
                    curnode.wildcardBranch = TrieNode()
                    curnode.wildcardBranch.parent = curnode
                curnode = curnode.wildcardBranch
            else:
                if (maskedValue & mask) == 0:  # zero bit
                    if curnode.zeroBranch is None:
                        curnode.zeroBranch = TrieNode()
                        curnode.zeroBranch.parent = curnode
                    curnode = curnode.zeroBranch
                else: # one bit
                    if curnode.oneBranch is None:
                        curnode.oneBranch = TrieNode()
                        curnode.oneBranch.parent = curnode
                    curnode = curnode.oneBranch

        return curnode

    def removeRule(self, node):
        parent = node.parent
        while parent is not None:
            if (parent.zeroBranch == node and \
                parent.oneBranch is None and \
                parent.wildcardBranch is None) or \
                (parent.oneBranch == node and \
                 parent.zeroBranch is None and \
                 parent.wildcardBranch is None) or \
                (parent.wildcardBranch == node and \
                 parent.zeroBranch is None and \
                 parent.oneBranch is None):
                tempparent = parent.parent
                node = parent
                parent = tempparent
            else:
                if parent.zeroBranch == node:
                    parent.zeroBranch = None
                elif parent.oneBranch == node:
                    parent.oneBranch = None
                elif parent.wildcardBranch == node:
                    parent.wildcardBranch = None
                break

        self.totalRuleCount -= 1
        if parent is None:
            self.root = None
            self.totalRuleCount = 0

    @classmethod
    def getForwardingGraph(cls, currentIndex, inTries, eqclass):
        graph = ForwardingGraph()

        if currentIndex + 1 != HeaderField.End:
            raise Exception("getForwardingTable() called on wrong trie")

        fieldValue = eqclass.lowerBound[currentIndex]
        fieldMask = HeaderField.MaxValue[currentIndex]
        maskedValue = fieldValue & fieldMask

        width = HeaderField.Width[currentIndex]

        for it in inTries:
            if it.totalRuleCount == 0:
                continue

            currLevelNodes = []
            nextLevelNodes = []
            currLevelNodes.append(it.root)

            for i in range(width):
                while len(currLevelNodes) > 0:
                    curnode = currLevelNodes.pop()

                    if curnode is None:
                        raise Exception("invalid node")

                    maskBit = 1 << ((width - 1) - i)
                    if fieldMask & maskBit == 0:  # wildcard bits
                        if curnode.zeroBranch is not None:
                            nextLevelNodes.append(curnode.zeroBranch)
                        if curnode.oneBranch is not None:
                            nextLevelNodes.append(curnode.oneBranch)
                        if curnode.wildcardBranch is not None:
                            nextLevelNodes.append(curnode.wildcardBranch)
                    else:
                        if maskedValue & maskBit == 0:  # zero bit
                            if curnode.zeroBranch is not None:
                                nextLevelNodes.append(curnode.zeroBranch)
                            if curnode.wildcardBranch is not None:
                                nextLevelNodes.append(curnode.wildcardBranch)
                        else:  # one bit
                            if curnode.oneBranch is not None:
                                nextLevelNodes.append(curnode.oneBranch)
                            if curnode.wildcardBranch is not None:
                                nextLevelNodes.append(curnode.wildcardBranch)

                currLevelNodes = nextLevelNodes
                nextLevelNodes = []

            for node in currLevelNodes:
                if node.ruleSet is not None:
                    for rule in node.ruleSet:
                        if rule.ruleType != Rule.FORWARDING:
                            continue

                        if rule.priority == Rule.INVALID_PRIORITY:
                            continue

                        link = ForwardingLink(rule)

                        # here, VeriFlow distinguishes between test and proxy mode
                        # no proxy mode here, so skip
                        if rule.location == rule.nextHop:
                            link.isGateway = True

                        graph.addLink(link)
                else:
                    raise Exception("Invalid node, ruleSet is None")

        return graph

    def getEquivalenceClasses(self, rule):
        packetClasses = []
        if self.root is None:
            return

        fieldInt = HeaderField.intValue(self.fieldIndex, rule.fieldValue[self.fieldIndex])
        maskInt = HeaderField.intValue(self.fieldIndex, rule.fieldMask[self.fieldIndex])
        maskedValue = fieldInt & maskInt

        width = HeaderField.Width[self.fieldIndex]
        curnode = self.root
        eqrange = EquivalenceRange()

        for i in range(width):
            mask = 1 << ((width - 1) - i)

            if (maskInt & mask) != 0:  # non-wildcard bit
                if (maskedValue & mask) == 0:   # zero bit
                    if curnode.zeroBranch is not None:
                        curnode = curnode.zeroBranch
                    else:
                        raise Exception("curnode.zeroBranch cannot be null")
                else:  # one bit
                    eqrange.lowerBound |= 1
                    eqrange.upperBound |= 1

                    if curnode.oneBranch is not None:
                        curnode = curnode.oneBranch
                    else:
                        raise Exception("curnode.oneBranch cannot be null")

                eqrange.lowerBound <<= 1
                eqrange.upperBound <<= 1
            else:  # wildcard bit
                break

        self.lowerBoundList = []
        self.lowerBoundMap = {}
        self.upperBoundList = []
        self.upperBoundMap = {}

        # perform dfs
        nodes = []
        nodes.append(curnode)
        ranges = []
        ranges.append(eqrange)

        while len(nodes) > 0:
            curnode = nodes.pop()
            temprange = ranges.pop()

            if curnode is None:
                raise Exception("Invalid node found")

            if curnode.oneBranch is not None:
                onerange = temprange.copy()
                onerange.lowerBound |= 1
                onerange.upperBound |= 1
                onerange.lowerBound <<= 1
                onerange.upperBound <<= 1
                ranges.append(onerange)
                nodes.append(curnode.oneBranch)

            if curnode.zeroBranch is not None:
                zerorange = temprange.copy()
                zerorange.lowerBound <<= 1
                zerorange.upperBound <<= 1
                ranges.append(zerorange)
                nodes.append(curnode.zeroBranch)

            if curnode.wildcardBranch is not None:
                wcrange = temprange.copy()
                wcrange.upperBound |= 1
                wcrange.lowerBound <<= 1
                wcrange.upperBound <<= 1
                ranges.append(wcrange)
                nodes.append(curnode.wildcardBranch)

            if curnode.ruleSet is not None:  # reached a leaf
                temprange.lowerBound >>= 1
                temprange.upperBound >>= 1

                self.addToBoundList(temprange.lowerBound,
                                    temprange.upperBound)
            elif curnode.nextLevelTrie is not None: # leaf
                temprange.lowerBound >>= 1
                temprange.upperBound >>= 1

                self.addToBoundList(temprange.lowerBound,
                                    temprange.upperBound)

        self.lowerBoundList.sort()
        self.upperBoundList.sort()

        lb = 0
        ub = 0

        if len(self.lowerBoundList) > 0:
            lb = self.lowerBoundList[0]
            ub = self.lowerBoundList[0]

        while len(self.upperBoundList) > 0:
            if len(self.lowerBoundList) > 0:
                lb = self.lowerBoundList[0]
                if lb > (ub + 1):
                    lb = ub + 1

                    if self.lowerBoundList[0] <= self.upperBoundList[0]:
                        ub = self.lowerBoundList[0] - 1
                    else:
                        ub = self.upperBoundList[0]
                        self.upperBoundList = self.upperBoundList[1:]

                    pktclass = EquivalenceClass()
                    pktclass.lowerBound[self.fieldIndex] = lb
                    pktclass.upperBound[self.fieldIndex] = ub

                    packetClasses.append(pktclass)
                    continue
                else:
                    self.lowerBoundList = self.lowerBoundList[1:]
            else:
                lb = ub + 1

            if len(self.lowerBoundList) > 0:
                if self.lowerBoundList[0] <= self.upperBoundList[0]:
                    ub = self.lowerBoundList[0] - 1
                else:
                    ub = self.upperBoundList[0]
                    self.upperBoundList = self.upperBoundList[1:]
            else:
                ub = self.upperBoundList[0]
                self.upperBoundList = self.upperBoundList[1:]

            pktclass = EquivalenceClass()
            pktclass.lowerBound[self.fieldIndex] = lb
            pktclass.upperBound[self.fieldIndex] = ub
            packetClasses.append(pktclass)

        return packetClasses

    @classmethod
    def getNextLevelEquivalenceClasses(cls, curIndex, lb, rule, inputTries):
        packetClasses = []
        outputTries = []

        nextIndex = curIndex + 1
        assert nextIndex < HeaderField.End

        fieldInt = lb
        maskInt = HeaderField.MaxValue[curIndex]
        maskedValue = fieldInt & maskInt

        for t in range(len(inputTries)):
            inputTrie = inputTries[t]
            if inputTrie.totalRuleCount == 0:
                continue

            curLevelNodes = []
            nextLevelNodes = []
            curLevelNodes.append(inputTrie.root)
            curnode = None

            width = HeaderField.Width[curIndex]
            for i in range(width):
                while len(curLevelNodes) > 0:
                    curnode = curLevelNodes[0]
                    curLevelNodes = curLevelNodes[1:]

                    if curnode is None:
                        raise Exception("invalid node")

                    mask = 1 << ((width - 1) - i)
                    if (maskInt & mask) == 0: # wildcard bit
                        if curnode.zeroBranch is not None:
                            nextLevelNodes.append(curnode.zeroBranch)
                        if curnode.oneBranch is not None:
                            nextLevelNodes.append(curnode.oneBranch)
                        if curnode.wildcardBranch is not None:
                            nextLevelNodes.append(curnode.wildcardBranch)
                    else:
                        if (maskedValue & mask) == 0: # zero bit
                            if curnode.zeroBranch is not None:
                                nextLevelNodes.append(curnode.zeroBranch)
                            if curnode.wildcardBranch is not None:
                                nextLevelNodes.append(curnode.wildcardBranch)
                        else: # one bit
                            if curnode.oneBranch is not None:
                                nextLevelNodes.append(curnode.oneBranch)
                            if curnode.wildcardBranch is not None:
                                nextLevelNodes.append(curnode.wildcardBranch)

                curLevelNodes = nextLevelNodes
                nextLevelNodes = []

            for i in range(len(curLevelNodes)):
                node = curLevelNodes[i]
                if node.nextLevelTrie is not None:
                    outputTries.append(node.nextLevelTrie)
                else:
                    raise Exception("invalid node")

        # found next level tries, now compute equivalence classes
        lblist = []
        ublist = []
        lbmap = {}
        ubmap = {}

        fieldInt = HeaderField.intValue(nextIndex, rule.fieldValue[nextIndex])
        maskInt = HeaderField.intValue(nextIndex, rule.fieldMask[nextIndex])
        maskedValue = fieldInt & maskInt

        for t in range(len(outputTries)):
            matchFound = True
            outputTrie = outputTries[t]
            if outputTrie.totalRuleCount == 0:
                continue

            width = HeaderField.Width[nextIndex]
            curnode = outputTrie.root
            eqrange = EquivalenceRange()

            for i in range(width):
                mask = 1 << ((width - 1) - i)

                if (maskInt & mask) != 0: # non-wildcard bit
                    if (maskedValue & mask) == 0:  #zero bit
                        if curnode.zeroBranch is not None:
                            curnode = curnode.zeroBranch
                        else:
                            matchFound = False
                            break
                    else:
                        eqrange.lowerBound |= 1
                        eqrange.upperBound |= 1

                        if curnode.oneBranch is not None:
                            curnode = curnode.oneBranch
                        else:
                            matchFound = False


                    eqrange.lowerBound <<= 1
                    eqrange.upperBound <<= 1
                else: # wildcard bit
                    matchFound = True

            if not matchFound:
                continue

            # perform DFS
            nodes = []
            nodes.append(curnode)
            ranges = []
            ranges.append(eqrange)

            while len(nodes) > 0:
                curnode = nodes.pop()
                temprange = ranges.pop()

                if curnode is None:
                    raise Exception("Invalid node found")

                if curnode.oneBranch is not None:
                    onerange = temprange.copy()
                    onerange.lowerBound |= 1
                    onerange.upperBound |= 1
                    onerange.lowerBound <<= 1
                    onerange.upperBound <<= 1
                    ranges.append(onerange)
                    nodes.append(curnode.oneBranch)

                if curnode.zeroBranch is not None:
                    zerorange = temprange.copy()
                    zerorange.lowerBound <<= 1
                    zerorange.upperBound <<= 1
                    ranges.append(zerorange)
                    nodes.append(curnode.zeroBranch)

                if curnode.wildcardBranch is not None:
                    wcrange = temprange.copy()
                    wcrange.upperBound |= 1
                    wcrange.lowerBound <<= 1
                    wcrange.upperBound <<= 1
                    ranges.append(wcrange)
                    nodes.append(curnode.wildcardBranch)

                if curnode.nextLevelTrie is not None or \
                   curnode.ruleSet is not None:      # reached a leaf
                    temprange.lowerBound >>= 1
                    temprange.upperBound >>= 1
                    Trie.addToBoundListEx(temprange.lowerBound,
                                          temprange.upperBound,
                                          lblist,
                                          ublist,
                                          lbmap,
                                          ubmap)
                else:
                    pass

        lblist.sort()
        ublist.sort()

        lb = 0
        ub = 0

        if len(lblist) > 0:
            lb = lblist[0]
            ub = ublist[0]

        while len(ublist) > 0:
            if len(lblist)  > 0:
                lb = lblist[0]
                if lb > (ub + 1):
                    lb = ub + 1

                    if lblist[0] <= ublist[0]:
                        ub = lblist[0] - 1
                    else:
                        ub = ublist[0]
                        ublist = ublist[1:]

                    pktclass = EquivalenceClass()
                    pktclass.lowerBound[nextIndex] = lb
                    pktclass.upperBound[nextIndex] = ub
                    packetClasses.append(pktclass)
                    continue
                else:
                    lblist = lblist[1:]
            else:
                lb = ub + 1

            if len(lblist) > 0:
                if lblist[0] <= ublist[0]:
                    ub = lblist[0] - 1
                else:
                    ub = ublist[0]
                    ublist = ublist[1:]
            else:
                ub = ublist[0]
                ublist = ublist[1:]

            pktclass = EquivalenceClass()
            pktclass.lowerBound[nextIndex] = lb
            pktclass.upperBound[nextIndex] = ub
            packetClasses.append(pktclass)

        return (outputTries, packetClasses)

    def addToBoundList(self, lb, ub):
        if lb not in self.lowerBoundMap:
            self.lowerBoundList.insert(0, lb)
            self.lowerBoundMap[lb] = ub
        else:
            if self.lowerBoundMap[lb] < ub:
                self.lowerBoundMap[lb] = ub

        if ub not in self.upperBoundMap:
            self.upperBoundList.insert(0, ub)
            self.upperBoundMap[ub] = lb
        else:
            if self.upperBoundMap[ub] > lb:
                self.upperBoundMap[ub] = lb


    @classmethod
    def addToBoundListEx(cls, lb, ub, lblist, ublist, lbmap, ubmap):
        if lb not in lbmap:
            lblist.insert(0, lb)
            lbmap[lb] = ub
        else:
            if lbmap[lb] < ub:
                lbmap[lb] = ub

        if ub not in ubmap:
            ublist.insert(0, ub)
            ubmap[ub] = lb
        else:
            if ubmap[ub] > lb:
                ubmap[ub] = lb

    def tostr(self):
        return self.traversePreorder(self.root, self.fieldName, 0, -1)

    def traversePreorder(self, node, fname, level, branch):
        if node is None:
            return ""

        linePrefix = "-" * level
        leadingSpace = " " * level

        string = linePrefix

        if branch == -1:
            string += fname
        else:
            string += str(branch)

        if node.ruleSet is not None:
            for r in node.ruleSet:
                string += "\n{0} {1}".format(leadingSpace, r)

        if node.nextLevelTrie is not None:
            string += str(node.nextLevelTrie)

        string += "\n"
        string += self.traversePreorder(node.zeroBranch, fname, level + 1, 0)
        string += self.traversePreorder(node.oneBranch, fname, level + 1, 1)
        string += self.traversePreorder(node.wildcardBranch, fname, level + 1, 2)
        return string

class MultilevelTrie(object):
    def __init__(self):
        self.primaryTrie = Trie(0)

    def addRule(self, rule):
        curTrie = self.primaryTrie
        tries = []

        for i in range(HeaderField.End):
            tries.append(curTrie)
            leaf = curTrie.addRule(rule)

            # if last level trie, need to check rule list
            if i == (HeaderField.End - 1):
                if leaf.ruleSet is None:
                    leaf.ruleSet = []
                else:
                    if rule in leaf.ruleSet:
                        logger.warning("Rule already exists")
                        return False

                leaf.ruleSet.append(rule)
            else:
                if leaf.nextLevelTrie is None:  # intermediate trie
                    leaf.nextLevelTrie = Trie(i + 1)

                curTrie = leaf.nextLevelTrie

        for t in tries:
            t.totalRuleCount += 1

        return True

    def delRule(self, rule):
        curTrie = self.primaryTrie
        tries = []
        leaves = []

        for i in range(HeaderField.End):
            leaf = curTrie.findNode(rule.fieldValue[i], rule.fieldMask[i])
            if leaf is None:
                return False
                #continue

            # if last level trie, need to check rule list
            if i == (HeaderField.End - 1):
                if leaf.ruleSet is None:
                    raise Exception("leaf.ruleSet cannot be None")

                if rule in leaf.ruleSet:
                    leaf.ruleSet.remove(rule)

                    for j, v in enumerate(leaves):
                        idx = len(leaves) - j - 1
                        if leaves[idx].nextLevelTrie.totalRuleCount == 0:
                            tries[idx].removeRule(leaves[idx])

                    return True

                return False
            else: # intermediate trie
                tries.append(curTrie)
                leaves.append(leaf)

                if leaf.nextLevelTrie is None:
                    raise Exception("leaf.nextLevelTrie cannot be None")

                curTrie = leaf.nextLevelTrie

        return False

    def _recGetAffected(self, rule, curIndex, prevClass, prevTries):
        if curIndex == HeaderField.End - 1:
            pc = EquivalenceClass()
            for i in range(HeaderField.End):
                c = prevClass[i]
                pc.lowerBound[i] = c.lowerBound[i]
                pc.upperBound[i] = c.upperBound[i]
            return (prevTries[-1], pc)
        else:
            if rule.ruleType == Rule.FORWARDING:
                tries, classes = Trie.getNextLevelEquivalenceClasses(
                    curIndex,
                    prevClass[-1].lowerBound[curIndex],
                    rule,
                    prevTries[-1])

                if len(classes) == 0:
                    field = HeaderField.fieldName(curIndex+1)
                    raise Exception("Error: 0 {0} packet classes".format(field))
                else:
                    ret = []
                    for c in classes:
                        pc = self._recGetAffected(rule,
                                                  curIndex+1,
                                                  prevClass + [c],
                                                  prevTries + [tries])

                        if isinstance(pc, list):
                            ret.extend(pc)
                        else:
                            ret.append(pc)

                    return ret

    def getAffectedEquivalenceClasses(self, rule, command):
        finalPacketClasses = []
        finalTries = []

        if command == OFPFC_ADD:
            result = self.addRule(rule)
            if not result:
                raise Exception("Error in addRule()")
        elif command == OFPFC_DELETE_STRICT:
            result = self.delRule(rule)
            if not result:
                raise Exception("Error in delRule()")
                return

            self.addRule(dummyRule)

        classes = self.primaryTrie.getEquivalenceClasses(rule)
        return self._recGetAffected(rule,
                                    0,
                                    classes,
                                    [[self.primaryTrie]])

    def getForwardingGraph(self, tries, eqclass):
        return Trie.getForwardingGraph(HeaderField.End - 1, tries, eqclass)

    def getAllEquivalenceClasses(self):
        classes = []
        dummyRule = Rule()
        dummyRule.ruleType = Rule.FORWARDING
        return self.getAffectedEquivalenceClasses(dummyRule, OFPFC_ADD)
