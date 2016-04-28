#!/usr/bin/env python

# Ubuntu install:
# python-ipaddr

import ipaddr
import socket
import struct
from netaddr import *

FieldIndex = { "IN_PORT": 0,
               "DL_SRC" : 1,
               "DL_DST" : 2,
               "DL_TYPE" : 3,
               "NW_SRC" : 4,
               "NW_DST" : 5, }

#               "FIELD_END" : 6,
#               "METADATA" : 7,
#               "WILDCARD" : 8 }

FIELD_END = 6 #len(FieldIndex.keys())

def getIndex(idx):
    for k,v in FieldIndex.iteritems():
        if v == idx:
            return k

#FieldWidth = { 0: 16,
#               1 : 48,
#               2 : 48,
#               3 : 16,
#               4 : 32,
#               5 : 32 ,
#               6 : 0 }

FieldWidth = { "IN_PORT" : 16,
               "DL_SRC" : 48,
               "DL_DST" : 48,
               "DL_TYPE" : 16,
               "NW_SRC" : 32,
               "NW_DST" : 32 ,
               "FIELD_END" : 0 }

def ip_to_binstr(ip):
    return bin(int(ipaddr.IPv4Address(ip)))[2::]

def iptoi(ip):
    # handle default value
    if ip == "0":
        return 0
    return int(ipaddr.IPv4Address(ip))

def itoip(i):
    return socket.inet_ntoa(struct.pack("!I", i))

def mac_to_binstr(mac):
    return EUI(mac).bits().replace("-", "")

def mactoi(mac):
    # handle default value
    if mac == "0":
        return 0
    return int(mac_to_binstr(mac))

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
            lowerBound = [0] * FIELD_END
        if upperBound is None:
            upperBound = [0] * FIELD_END

        assert len(lowerBound) == len(upperBound)
        for i in range(len(lowerBound)):
            assert lowerBound[i] <= upperBound[i]

        self.lowerBound = list(lowerBound)
        self.upperBound = list(upperBound)

    def getRange(self, findex):
        assert findex <= len(self.lowerBound)
        return self.upperBound[findex] - self.lowerBound[findex]

    def getMaxValue(findex):
        if findex == FieldIndex['IN_PORT']:
            return int(0xFFFF)
        elif findex == FieldIndex['DL_SRC']:
            return int(0xFFFFFFFFFFFF)
        elif findex == FieldIndex['DL_DST']:
            return int(0xFFFFFFFFFFFF)
        elif findex == FieldIndex['DL_TYPE']:
            return int(0xFFFF)
        elif findex == FieldIndex['NW_SRC']:
            return int(0xFFFFFFFF)
        elif findex == FieldIndex['NW_DST']:
            return int(0xFFFFFFFF)
        else:
            raise ValueError("wrong field index")

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
        self.fieldValue = [0] * FIELD_END
        self.fieldMask = [0] * FIELD_END
        self.ruleType = Rule.DUMMY
        self.priority = Rule.INVALID_PRIORITY
        self.wildcards = 0
        self.location = None
        self.nextHop = None

    def getEquivalenceClass(self):
        lb = [0] * FIELD_END
        ub = [0] * FIELD_END

        for fname, findex in FieldIndex.iteritems():
            fieldValue = 0
            fieldMask = 0

            if fname == 'DL_SRC' or fname == 'DL_DST':
                fieldValue = mactoi(self.fieldValue[findex])
                fieldMask = mactoi(self.fieldMask[findex])
            elif fname == 'NW_SRC' or fname == 'NW_DST':
                fieldValue = iptoi(self.fieldValue[findex])
                fieldMask = iptoi(self.fieldMask[findex])
            else:
                fieldValue = int(self.fieldValue[findex])
                fieldMask = int(self.fieldMask[findex])

            maskedValue = fieldValue & fieldMask

            for j in range(FieldWidth[fname]):
                lb[findex] <<= 1
                ub[findex] <<= 1

                width = FieldWidth[fname]
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
        findex = FieldIndex[fname]
        eqrange = EquivalenceRange()

        fieldValue = 0
        fieldMask = 0
        
        if findex == FieldIndex['DL_SRC'] or findex == FieldIndex['DL_DST']:
            fieldValue = mactoi(self.fieldValue[findex])
            fieldMask = mactoi(self.fieldMask[findex])
        elif findex == FieldIndex['NW_SRC'] or findex == FieldIndex['NW_DST']:
            fieldValue = iptoi(self.fieldValue[findex])
            fieldMask = iptoi(self.fieldMask[findex])
        else:
            fieldValue = int(self.fieldValue[findex])
            fieldMask = int(self.fieldValue[findex])

        maskedValue = fieldValue & fieldMask

        for j in range(FieldWidth[fname]):
            eqrange.lowerBound <<= 1
            eqrange.upperBound <<= 1

            maskBit = 1 << ((FieldWidth[fname] - 1) - j)
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
            for i in range(FIELD_END):
                if self.fieldValue[i] != other.fieldValue[i] or \
                   self.fieldMask[i] != other.fieldMask[i]:
                    return False
            return True
        else:
            return False

    def __repr__(self):
        return str(self)

    def __str__(self):
        # TODO: 
        return "Value: {0}, Mask: {1}".format(self.fieldValue, self.fieldMask)

class TrieNode(object):
    def __init__(self):
        self.parent = None
        self.zeroBranch = None
        self.oneBranch = None
        self.wildcardBranch = None
        self.nextLevelTrie = None
        self.ruleSet = None # key=Rule, Hash=KHash<rule>

class Trie(object):
    def __init__(self, fname): #fieldIndex):
        self.root = None
        self.fieldName = fname
        self.fieldIndex = FieldIndex[fname]
        self.totalRuleCount = 0

    def getIntValue(self, findex, valueOrMask):
        if findex == FieldIndex["DL_SRC"] or findex == FieldIndex["DL_DST"]:
            return mactoi(valueOrMask)
        elif findex == FieldIndex["NW_SRC"] or findex == FieldIndex["NW_DST"]:
            return iptoi(valueOrMask)
        else:
            return int(valueOrMask)

    def findNode(self, fieldValue, fieldMask):
        if self.root is None or self.totalRuleCount == 0:
            return None

        fieldInt = self.getIntValue(self.fieldIndex, fieldValue)
        maskInt = self.getIntValue(self.fieldIndex, fieldMask)
        maskedValue = fieldInt & maskInt

        width = FieldWidth[self.fieldName]
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

        fieldInt = self.getIntValue(self.fieldIndex, rule.fieldValue[self.fieldIndex])
        maskInt = self.getIntValue(self.fieldIndex, rule.fieldMask[self.fieldIndex])
        maskedValue = fieldInt & maskInt

        width = FieldWidth[self.fieldName]
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

    def getEquivalenceClasses(self, rule):
        packetClasses = []
        if self.root is None:
            return

        fieldInt = self.getIntValue(self.fieldIndex, rule.fieldValue[self.fieldIndex])
        maskInt = self.getIntValue(self.fieldIndex, rule.fieldMask[self.fieldIndex])
        maskedValue = fieldInt & maskInt

        width = FieldWidth[self.fieldName]
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
                # TODO: should use copy here?
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

    def getNextLevelEquivalenceClass(self, curIndex, lb, rule, inputTries):
        packetClasses = []
        outputTries = []

        if self.root is None:
            return

        nextIndex = curIndex + 1
        assert nextIndex < "FIELD_END"

        fieldInt = lb
        maskInt = EquivalenceClass.getMaxValue(curIndex)
        maskedValue = fieldInt & maskInt

        for t in range(len(inputTries)):
            inputTrie = inputTries[t]
            if inputTrue.totalRuleCount == 0:
                continue

            curLevelNodes = []
            nextLevelNodes = []
            curLevelNodes.append(inputTrie.root)
            curnode = None

            # TODO: refactor
            width = FieldWidth[getIndex(curIndex)]
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
                                nextLevelNodes.append(wildcardBranch)

                curLevelNodes = nextLevelNodes
                # TODO: is this right? Veriflow erase(0, end)
                nextLevelNodes = []

            for i in range(len(curLevelNodes)):
                node = curLevelNodes[i]
                if node.nextLevelTrie is not None:
                    outputTries.append(node.nextLevelTrie)
                else:
                    raise Exception("invalid node")

            # right indent?
            
        # found next level tries, now compute equivalence classes
        # TODO: fix below
        lblist = []
        ublist = []
        lbmap = {}
        ubmap = {}

        fieldInt = self.getIntValue(nextIndex, rule.fieldValue[nextIndex])
        maskInt = self.getIntValue(nextIndex, rule.fieldMask[nextIndex])
        maskedValue = fieldInt & maskInt

        for t in len(outputTries):
            matchFound = True
            outputTrie = outputTries[t]
            if outputTrie.totalRuleCount() == 0:
                continue

            # TODO: refactor
            width = FieldWidth[getIndex(nextIndex)]
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
                    # TODO: should use copy here?
                    onerange = temprange.copy()
                    onerange.lowerBound |= 1
                    oneRange.upperBound |= 1
                    oneRange.lowerBound <<= 1
                    oneRange.upperBound <<= 1
                    ranges.append(onerange)
                    nodes.append(curnode.oneBranch)

                if curnode.zeroBranch is not None:
                    zerorange = temprange.copy()
                    zerorange.lowerBonud <<= 1
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
                   cuurnode.ruleSet is not None:      # reached a leaf
                    temprange.lowerBound >>= 1
                    temprange.upperBound >>= 1
                    self.addToBoundListEx(temprange.lowerBound,
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
            lb = lowerBoundList[0]
            ub = lowerBoundList[0]

        while len(upperBoundList) > 0:
            if len(lowerBoundList)  > 0:
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
            pktclass.lowerBound[nextIndex] = lowerBound
            pktclass.upperBound[nextIndes] = upperBound
            packetClasses.append(pktclass)

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


    def addToBoundListEx(self, lb, ub, lblist, ublist, lbmap, ubmap):
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
        
def vf_addflow(primaryTrie, rule):
    curTrie = primaryTrie
    tries = []

    for i in range(FIELD_END):
        tries.append(curTrie)
        leaf = curTrie.addRule(rule)
        
        # if last level trie, need to check rule list
        if i == (FIELD_END - 1):
            if leaf.ruleSet is None:
                leaf.ruleSet = []
            else:
                if rule in leaf.ruleSet:  # already exists
                    return False

            leaf.ruleSet.append(rule)
        else:
            if leaf.nextLevelTrie is None:  # intermediate trie
                leaf.nextLevelTrie = Trie(getIndex(i + 1))

            curTrie = leaf.nextLevelTrie

    for t in tries:
        t.totalRuleCount += 1

def vf_delflow(primaryTrie, rule):
    curTrie = primaryTrie
    tries = []
    leaves = []

    for i in range(FIELD_END):
        leaf = curTrie.findNode(rule.fieldValue[i], rule.fieldMask[i])
        if leaf is None:
            return False
            #continue

        # if last level trie, need to check rule list        
        if i == (FIELD_END - 1):
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

def sim():
    primaryTrie = None
    
def test_ec():
    e = EquivalenceRange([0, 1, 2], [1, 2, 3])
    print e

    lb = [0,
          mactoi('00-00-00-00-00-00'),
          mactoi('00-00-00-00-00-00'),
          0x00,
          iptoi('192.168.0.1'),
          iptoi('192.168.0.2')]
    ub = [1,
          mactoi('00-00-00-00-00-01'),
          mactoi('00-00-00-00-00-02'),
          0x00,
          iptoi('192.168.0.2'),
          iptoi('192.168.0.4')]

    e = EquivalenceClass(lb, ub)
    f = EquivalenceClass(lb, ub)
    assert (e == f) == True
    print e.getRange(FieldIndex["NW_SRC"])
    print e.getRange(FieldIndex["DL_SRC"])
    assert e.getRange(FieldIndex["IN_PORT"]) == 1


def test_binaddr():
    mac = mac_to_binstr('00-1B-77-49-54-FD')
    ip = ip_to_binstr('192.168.1.1')

    print len(mac)
    print mac
    print len(ip)
    print ip

def test_rule():
    r1 = Rule()

    r1.ruleType = Rule.FORWARDING
    r1.fieldValue[FieldIndex["NW_SRC"]] = iptoi("192.168.1.20")
    r1.fieldMask[FieldIndex["NW_SRC"]] = iptoi("255.255.255.0")

    eclass = r1.getEquivalenceClass()
    print "R1 EC: ", itoip(eclass.lowerBound[FieldIndex["NW_SRC"]]), itoip(eclass.upperBound[FieldIndex["NW_SRC"]])
    er = r1.getEquivalenceRange("NW_SRC")
    print itoip(er.lowerBound), itoip(er.upperBound)


def test_trie():
    r1 = Rule()

    r1.ruleType = Rule.FORWARDING
    r1.fieldValue[FieldIndex["NW_SRC"]] = iptoi("192.168.1.20")
    r1.fieldMask[FieldIndex["NW_SRC"]] = iptoi("255.255.255.255")

    t = Trie("NW_SRC")
    # n = t.addRule(r1)
    # t.totalRuleCount += 1
    # print n

    vf_addflow(t, r1)
    print t.totalRuleCount

    # n = t.findNode(iptoi("192.168.1.20"), iptoi("255.255.255.255"))
    # print n
    # # print t.tostr()

    vf_delflow(t, r1)
    print t.totalRuleCount

    print t.getEquivalenceClasses(r1)
    
def test():
#    test_ec()
    # print "Testing rule"
    # test_rule()

    print "Testing trie"
    test_trie()

if __name__ == "__main__":
    test()

#    temprange = EquivalenceRange(0, 1)
#    onerange = temprange
#    onerange.lowerBound = 0
#    zerorange = temprange
#    print onerange, zerorange


# TODO:
#  see VeriFlow.cpp on adding rule (adds ruleset to trienode)

# implement getForwardingGraph
# fix vf_delflow
