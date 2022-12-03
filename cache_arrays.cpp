/** $lic$
 * Copyright (C) 2012-2015 by Massachusetts Institute of Technology
 * Copyright (C) 2010-2013 by The Board of Trustees of Stanford University
 *
 * This file is part of zsim.
 *
 * zsim is free software; you can redistribute it and/or modify it under the
 * terms of the GNU General Public License as published by the Free Software
 * Foundation, version 2.
 *
 * If you use this software in your research, we request that you reference
 * the zsim paper ("ZSim: Fast and Accurate Microarchitectural Simulation of
 * Thousand-Core Systems", Sanchez and Kozyrakis, ISCA-40, June 2013) as the
 * source of the simulator in any publications that use this software, and that
 * you send us a citation of your work.
 *
 * zsim is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
 * FOR A PARTICULAR PURPOSE. See the GNU General Public License for more
 * details.
 *
 * You should have received a copy of the GNU General Public License along with
 * this program. If not, see <http://www.gnu.org/licenses/>.
 */

#include "cache_arrays.h"
#include "hash.h"
#include "repl_policies.h"
#include "zsim.h"

/* Set-associative array implementation */

SetAssocArray::SetAssocArray(uint32_t _numLines, uint32_t _assoc, ReplPolicy* _rp, HashFamily* _hf) : rp(_rp), hf(_hf), numLines(_numLines), assoc(_assoc)  {
    array = gm_calloc<Address>(numLines);
    numSets = numLines/assoc;
    setMask = numSets - 1;
    assert_msg(isPow2(numSets), "must have a power of 2 # sets, but you specified %d", numSets);
    partitionSetCount = numSets/(zinfo->numCores); 
    partitionMask = partitionSetCount - 1; 
    partitionAssoc = assoc/(zinfo->numCores); 
    if (partitionAssoc == 0) partitionAssoc=1;
}

int32_t SetAssocArray::lookup(const Address lineAddr, const MemReq* req, bool updateReplacement, uint32_t& secondSearch) {
    if(isLLC && zinfo->setPartition){

        //uint32_t set = hf->hash(0, lineAddr) & setMask;
        uint32_t set = (hf->hash(0, lineAddr) & partitionMask) + partitionSetCount*proc_partition;
        uint32_t first = set*assoc;
            
        for (uint32_t id = first; id < first + assoc; id++) {
            if (array[id] ==  lineAddr) {
                if (updateReplacement) rp->update(id, req);
                return id;
            }
        }
        return -1;


    }else if (isLLC && zinfo->wayPartition) {

       uint32_t set = hf->hash(0, lineAddr) & setMask;

       uint32_t low = set*assoc + ((proc_partition*partitionAssoc) & (assoc-1));
       uint32_t high = low + partitionAssoc ;
       for (uint32_t id = low; id < high; id++) {
          if (array[id] ==  lineAddr) {
              if (updateReplacement) rp->update(id, req);
              return id;
          }
       }
       return -1;


    }


    uint32_t set = hf->hash(0, lineAddr) & setMask;
    uint32_t first = set*assoc;
    for (uint32_t id = first; id < first + assoc; id++) {
        if (array[id] ==  lineAddr) {
            if (updateReplacement) rp->update(id, req);
            return id;
        }
    }
    return -1;
}

uint32_t SetAssocArray::preinsert(const Address lineAddr, const MemReq* req, Address* wbLineAddr,Address* firstAddr,uint32_t& candidate_2,bool& sec) { //TODO: Give out valid bit of wb cand?

    if (isLLC && zinfo->setPartition){

       uint32_t set = (hf->hash(0, lineAddr) & partitionMask) + partitionSetCount*proc_partition;
       uint32_t first = set*assoc;
       uint32_t candidate = rp->rankCands(req, SetAssocCands(first, first+assoc));

       *wbLineAddr = array[candidate];
       return candidate;
    
    } else if (isLLC && zinfo->wayPartition){

       uint32_t set = hf->hash(0, lineAddr) & setMask;
       uint32_t low = set*assoc + ((proc_partition*partitionAssoc) & (assoc -1));
       uint32_t high = low + partitionAssoc ;
       uint32_t candidate = rp->rankCands(req, SetAssocCands(low, high));

//       info ("Accessing candidate, low is %d, high is %d, selection is %d, set is %d, numSets is %d, proc partition is %d, partitionAssoc is %d\n", low, high, candidate, set, (int)numSets, (int)proc_partition, (int)partitionAssoc);

       *wbLineAddr = array[candidate];
       return candidate;

    }


    uint32_t set = hf->hash(0, lineAddr) & setMask;
    uint32_t first = set*assoc;
 //   info("high is %lu, total lines is %lu", (long unsigned)first+assoc, 
 //           (long unsigned)(numSets*assoc)     );
    uint32_t candidate = rp->rankCands(req, SetAssocCands(first, first+assoc));

    *wbLineAddr = array[candidate];
    return candidate;
}

void SetAssocArray::postinsert(const Address lineAddr, const MemReq* req, uint32_t candidate) {
    rp->replaced(candidate);
    array[candidate] = lineAddr;
    rp->update(candidate, req);
}

//*************************************************************//
/* EBSC Cache Implementation */
//
EBSCArray::EBSCArray(uint32_t _numLines, uint32_t _assoc, ReplPolicy* _rp, HashFamily* _hf_1,HashFamily* _hf_1_c, HashFamily* _hf_2, HashFamily* _hf_2_c)
    :numLines(_numLines),assoc(_assoc),rp(_rp),hf_1(_hf_1),hf_1_c(_hf_1_c),hf_2(_hf_2),hf_2_c(_hf_2_c){

    array = gm_calloc<Address>(numLines);
    array_reuse = gm_calloc<Address>(numLines);
    d_bit = gm_calloc<uint32_t>(numLines);

    // this value can be set for different parameter
    source_num = 3;
    hashlistNum = 4;

    numSets = numLines/assoc;
    switch_array = gm_calloc<int>(numSets);
    next_flag = gm_calloc<int>(numSets);
    
    hf_list = gm_calloc<HashFamily*>(hashlistNum);

    // create this hash_list

    hf_list[0] = new FeistelFamily(0x3D4267531A);
    hf_list[1] = new FeistelFamily(0xCAC7EAFFA1);
    hf_list[2] = new FeistelFamily(0x67089ddd34); 
    hf_list[3] = new FeistelFamily(0x7d28431474); 


    int32_t numSourceList = numSets * source_num;
    source_set = gm_calloc<SourceSet>(numSourceList);

    info ("Initializing the EBSC array\n");

    for(int i  = 0; i < (int)numLines;i++){
        d_bit[i] = 0;
    }

    for (int i=0; i< (int)numSets ; i++){
      switch_array[i]=0;
      next_flag[i] = 0;
    }

    // a list can maintain at most 3 source set;
    for (int i = 0; i < (int)numSourceList; i++){
        source_set[i].source_list = -1;
        source_set[i].source_counter = 0;
        source_set[i].encry_key = -1;
    }

    //assert(numSets == 2048);
    setMask = numSets - 1;
    assert_msg(isPow2(numSets), "must have a power of 2 # sets, but you specified %d", numSets);
    rng = new MTRand(0x322D2523F);
}


int32_t EBSCArray::lookup(const Address lineAddr, const MemReq* req, bool updateReplacement, uint32_t& secondSearch) {
    // init this value
    secondSearch = 0;

    uint32_t set0 = hf_1_c->hash(0, lineAddr) & setMask;
    uint32_t set1 = 0;

    // change the hash function
    // but should I change hf_1 or hf_2 or all of them ??
    if (switch_array[set0] == 1) { 
        set0 = hf_1->hash(0, lineAddr) & setMask;
        set1 = hf_2->hash(0, lineAddr) & setMask;
    }

    int* set_list = gm_calloc<int>(hashlistNum + 1);

    for(int i = 0; i < hashlistNum + 1; i++){
        if(i == 0){
            set_list[i] = hf_2_c->hash(0,lineAddr) & setMask;
        }else{
            set_list[i] = hf_list[i - 1]->hash(0,lineAddr) & setMask;
        }
    }
 
    

    //first search
    uint32_t first = set0*assoc;
    for (uint32_t id = first; id < first + assoc; id++) {
        // only search the first search data
        if (d_bit[id] == 0 && array[id] ==  lineAddr) {
            if (updateReplacement) 
                rp->update(id, req);
            return id;
        }
    }
   //second search
    int remapid = getRemapId(set0,set_list,set1);

    uint32_t second = set1*assoc;
    if(next_flag[set1] != 0 && remapid != -1){
        secondSearch = 1;

        for(uint32_t id = second; id < second + assoc; id++){
            if(d_bit[id] == (uint32_t)remapid && array[id] == lineAddr){
                if(updateReplacement)
                    rp->update(id,req);
                return id;
            }
        }
    }

    // the other mapping
    //for(int hi = 0; hi < hashlistNum; hi++){
    //    secondSearch = 1;
    //    if(next_flag[set_list[i]] != 0 && remapid_list[i] != -1){
    //        if(d_bit[id] == (uint32_t)remapid_list[i] && array[id] == lineAddr){
    //            if(updateReplacement)
    //                rp->update(id,req);
    //            return id;
    //        }
    //    }
    //}

    return -1;
}

void EBSCArray::updateStat(uint32_t set){
    // update the d_mask value
    next_flag[set] = 0;
    uint32_t first = set*assoc;
    for(uint32_t i = first; i < first + assoc; i++){
        if(d_bit[i] != 0){
            next_flag[set] = 1;
            break;
        }
    }

    int source_base = source_num * set;
    for(int i = source_base; i < source_base + source_num; i++){
        if(source_set[i].source_counter == 0 && source_set[i].source_list != -1){
           // std::cout << "clear source_set " << i << std::endl;
            source_set[i].source_list = -1;
            source_set[i].encry_key = -1;
        }
    }
}

uint64_t EBSCArray::getAddr(uint32_t set, int way){
   //get the addresses corresponding to the set
   //check that the addresses are correct
   uint32_t first = set*assoc;
   uint64_t lineAddr = array[first + way]; 
   return lineAddr;
}

int EBSCArray::getSwitch(uint32_t set){
   return (switch_array[set]);
}

int EBSCArray::setSwitch(uint32_t set){
   switch_array[set]=1;
   return 1;
}

uint32_t EBSCArray::getReplSet(uint64_t lineAddr){
  uint32_t set = hf_1->hash(0, lineAddr) & setMask;
  return set; 
}

// ??????
uint64_t EBSCArray::getReplAddr(uint32_t set){
  uint32_t candidate = set*assoc + (rng->randInt(assoc - 1) & (assoc -1));
  //info ("candidate is %d\n" , (int)candidate);
  return array[candidate]; 
}


uint64_t EBSCArray::getReplId(uint32_t set, uint32_t &lineId){
  uint32_t candidate = set*assoc + (rng->randInt(assoc - 1) & (assoc -1));
  lineId = candidate;
  //info ("candidate is %d\n" , (int)candidate);
  return array[candidate]; 
}
// ????


//uint32_t EBSCArray::secondSel(uint32_t mask){
//    if(mask == 6 || mask == 5 || mask == 3)
//        return (7-mask);
//    else if(mask == 0 || mask == 2 || mask ==4)
//        return 1;
//    else
//        return 2;
//}


// change this function for multi-mapping
int EBSCArray::allocSpace(int sset, int *set_list, uint32_t &tset){
    // judge if there is space for usr to alloc an id
    //int list_index = set * source_num;
    //for(int i = list_index ; i < list_index + source_num; i++){
    //    if(source_set[i].source_list == -1)
    //        return (i - list_index + 1);
    //}
    //return -1;
    for(int li = 0; li < hashlistNum + 1; li++){
        int list_index = set_list[li] * source_num;
        for(int i = list_index ; i < list_index + source_num; i++){
            if(source_set[i].source_list == -1 && sset != set_list[li]){
                tset = set_list[li];
                source_set[i].encry_key = li;
                return (i - list_index + 1);
            }
        }
    }

    tset = 0;
    return -1;
}

int EBSCArray::getRemapId(int sset, int *set_list, uint32_t &tset){
    
    // hashlistNum + hash->2
    for(int li = 0; li < hashlistNum + 1; li++){
        // cal the list base
        int list_index = set_list[li] * source_num;
        for(int i = list_index; i < list_index + source_num; i++){
            if(source_set[i].source_list == sset && source_set[i].encry_key == li){
                tset = set_list[li];
                return (i - list_index + 1);
            }
        }
    }
    tset = 0;
    return -1;

    //int list_index = remapSet * source_num;
    ////for(int i = list_index; i < list_index + source_num; i++){
    //for(int i = list_index ; i < list_index + source_num; i++){
    //    if(source_set[i].source_list == sset){
    //        return (i - list_index + 1);
    //    }
    //}
    //return -1;
    //assert_msg(false,"can't get an invalid remapid");
}

uint32_t EBSCArray::preinsert(const Address lineAddr, const MemReq* req, Address* wbLineAddr,Address* firstAddr, uint32_t& candidate_2,bool& sec) { //TODO: Give out valid bit of wb cand?
   // init the return value for evict
   
    if(lineAddr == 1347913){
        std::cout << "ok" << std::endl;
    }
    sec = false;    // indicate if this has second remap or not  first --> second lineId
    candidate_2 = 0;// the second lineID 
    *firstAddr = 0; // the value send to candidate_2

    uint32_t set0 = hf_1_c->hash(0,lineAddr) & setMask;

    // if remap, the hash funciton will change
    if(switch_array[set0] == 1){
        set0 = hf_2_c->hash(0,lineAddr) & setMask;
    }

    uint32_t first = set0*assoc;
    uint32_t candidate = rp->rankCands(req,SetAssocCands(first,first+assoc));
    Address FAddr = array[candidate];

    // get the second possible position
    //uint32_t set1 = hf_2_c->hash(0,FAddr) & setMask;
    //uint32_t source_base = set1 * source_num;
    //uint32_t second = set1*assoc;
    //int remapid = getRemapId(set0, set1);
    //if(remapid == -1){
    //    remapid = allocSpace(set1);
    //}

    // multi-mapping
    // ******************** //
    int* set_list = gm_calloc<int>(hashlistNum + 1);
    uint32_t setR = hf_1_c->hash(0,FAddr) & setMask;

    for(int i = 0; i < hashlistNum + 1; i++){
        if(i == 0){
            set_list[i] = hf_2_c->hash(0,FAddr) & setMask;
        }else{
            set_list[i] = hf_list[i - 1]->hash(0,FAddr) & setMask;
        }
    }
    uint32_t set1 = 0;
    int remapid = getRemapId(setR,set_list,set1);
    if(remapid == -1){
        remapid = allocSpace(setR,set_list,set1);
    }
    uint32_t source_base = set1 * source_num;
    uint32_t second = set1*assoc;

    // ******************* //

    //if(FAddr == 0 || d_bit[candidate] != 0 || remapid == -1 || set0 == set1){
    //    // this means the candidate is not full,so we just return this candidate 
    //    // 1. if the candidate is not full, should return the first candidate
    //    // 2. if the candidate is full, but we return an second-map candidate, should return the first candidate
    //    // 3. if there is no id space for user, should also return the first candidate
    //    // 4. there is an condition that, two hash function will map to the same cache line, so we do this
    //    *wbLineAddr = FAddr;
    //    if(d_bit[candidate] != 0){
    //        if(source_set[source_base + d_bit[candidate] - 1].source_list != -1){
    //            // means this id has some value
    //            source_set[source_base + d_bit[candidate] - 1].source_counter --;
    //        }
    //    }
    //    d_bit[candidate] = 0;
    if(FAddr == 0){
        *wbLineAddr = FAddr;
        d_bit[candidate] = 0;
    }else if(remapid == -1){
        *wbLineAddr = FAddr;
        if(d_bit[candidate] != 0){
            if(source_set[source_base + d_bit[candidate] - 1].source_list != -1){
                // means this id has some value
                source_set[source_base + d_bit[candidate] - 1].source_counter --;
            }
        }
        d_bit[candidate] = 0;
    }
    else if(d_bit[candidate] != 0){
        *wbLineAddr = FAddr;
        if(source_set[source_base + d_bit[candidate] - 1].source_list != -1){
            // means this id has some value
            source_set[source_base + d_bit[candidate] - 1].source_counter --;
        }
        d_bit[candidate] = 0;
    }else{
        // if we have use this id, we should maintain this, or we should allocate an new one
        sec = true;                                                                    
       // std::cout << "second set is " << set1 << std::endl;
        uint32_t candidate2 = rp->rankCands(req,SetAssocCands(second,second+assoc));   
        candidate_2 = candidate2;                                                      
        Address secAddr = array[candidate2];                                           
                                                                                       
        // update d_bit stats                                                          
        d_bit[candidate2] = remapid;                                              
        // update the source_list
        int source_index = source_base + remapid - 1;
        source_set[source_index].source_list = setR; 
        source_set[source_index].source_counter++;

      //  std::cout << "source_index = " << source_index << " = " << setR << std::endl; 

        *firstAddr  = FAddr;                                                           
        *wbLineAddr = secAddr;                                                         
    }                                                                              
    updateStat(set0);
    updateStat(set1);                                                                  
    return candidate;                                                                  
}

void EBSCArray::postinsert(const Address lineAddr, const MemReq* req, uint32_t candidate) {
    rp->replaced(candidate);
    array[candidate] = lineAddr;
    rp->update(candidate, req);
}

void EBSCArray::switchHash(){
   HashFamily *temp;
   temp = hf_1_c;
   hf_1_c = hf_1;
   hf_1 = temp;
   return;
}

void EBSCArray::resetSwitches(){
  for (int i=0; i<(int)numSets; i++){
    switch_array[i]=0;  
  }
}

void EBSCArray::moveAddr(Address repl_addr, uint32_t repl_id, Address lineAddr, uint32_t lineId){
  //switching the addresses
  //info ("lineId == %d", lineId);
  assert(array[repl_id] == repl_addr); 
  assert(array[lineId] == lineAddr); 
  

  array[repl_id] = lineAddr;
  array[lineId] = 0;

  return;
}



//*************************************************************//




/* CEASER Cache Implementation */
CEASERArray::CEASERArray(uint32_t _numLines, uint32_t _assoc, ReplPolicy* _rp, HashFamily* hf_1, HashFamily *hf_2) : rp(_rp), hf(hf_1), hf_current(hf_1), hf_target(hf_2), numLines(_numLines), assoc(_assoc)  {
    array = gm_calloc<Address>(numLines);
    array_reuse = gm_calloc<Address>(numLines);
    numSets = numLines/assoc;
    switch_array = gm_calloc<int>(numSets);

    info ("Initializing the CEASER array\n");

    for (int i=0; i< (int)numSets ; i++){
      switch_array[i]=0;
    }
    //assert(numSets == 2048);
    setMask = numSets - 1;
    assert_msg(isPow2(numSets), "must have a power of 2 # sets, but you specified %d", numSets);
    rng = new MTRand(0x322D2523F);
}

int32_t CEASERArray::lookup(const Address lineAddr, const MemReq* req, bool updateReplacement, uint32_t& secondSearch) {
    uint32_t set = hf_current->hash(0, lineAddr) & setMask;
    if (switch_array[set] == 1) { set = hf_target->hash(0, lineAddr) & setMask; }
    uint32_t first = set*assoc;
    for (uint32_t id = first; id < first + assoc; id++) {
        if (array[id] ==  lineAddr) {
            //if (updateReplacement) rp->update(id, req);
            return id;
        }
    }
    return -1;
}

uint64_t CEASERArray::getAddr(uint32_t set, int way){
   //get the addresses corresponding to the set
   //check that the addresses are correct
   uint32_t first = set*assoc;
   uint64_t lineAddr = array[first + way]; 
   return lineAddr;
}

int CEASERArray::getSwitch(uint32_t set){
   return (switch_array[set]);
}

int CEASERArray::setSwitch(uint32_t set){
   switch_array[set]=1;
   return 1;
}

uint32_t CEASERArray::getReplSet(uint64_t lineAddr){
  uint32_t set = hf_target->hash(0, lineAddr) & setMask;
  return set; 
}

uint64_t CEASERArray::getReplAddr(uint32_t set){
  uint32_t candidate = set*assoc + (rng->randInt(assoc - 1) & (assoc -1));
  //info ("candidate is %d\n" , (int)candidate);
  return array[candidate]; 
}


uint64_t CEASERArray::getReplId(uint32_t set, uint32_t &lineId){
  uint32_t candidate = set*assoc + (rng->randInt(assoc - 1) & (assoc -1));
  lineId = candidate;
  //info ("candidate is %d\n" , (int)candidate);
  return array[candidate]; 
}


uint32_t CEASERArray::preinsert(const Address lineAddr, const MemReq* req, Address* wbLineAddr, Address* firstAddr,uint32_t& candidate_2,bool& sec) { //TODO: Give out valid bit of wb cand?
    uint32_t set = hf_current->hash(0, lineAddr) & setMask;
    if (switch_array[set] == 1) { set = hf_target->hash(0, lineAddr) & setMask; }
    uint32_t first = set*assoc;

    //uint32_t candidate = rp->rankCands(req, SetAssocCands(first, first+assoc));
    uint32_t candidate = first +  (rng->randInt(assoc - 1) & (assoc -1));
    *wbLineAddr = array[candidate];
    return candidate;
}

void CEASERArray::postinsert(const Address lineAddr, const MemReq* req, uint32_t candidate) {
    //rp->replaced(candidate);
    array[candidate] = lineAddr;
    //rp->update(candidate, req);
}

void CEASERArray::switchHash(){
   HashFamily *temp;
   temp = hf_current;
   hf_current = hf_target;
   hf_target = temp;
   return;
}

void CEASERArray::resetSwitches(){
  for (int i=0; i<(int)numSets; i++){
    switch_array[i]=0;  
  }
}

void CEASERArray::moveAddr
        (Address repl_addr, uint32_t repl_id, 
         Address lineAddr, uint32_t lineId){
  //switching the addresses
  //info ("lineId == %d", lineId);
  assert(array[repl_id] == repl_addr); 
  assert(array[lineId] == lineAddr); 
  

  array[repl_id] = lineAddr;
  array[lineId] = 0;

  return;
}


/* ZCache implementation */

ZArray::ZArray(uint32_t _numLines, uint32_t _ways, uint32_t _candidates, ReplPolicy* _rp, HashFamily* _hf) //(int _size, int _lineSize, int _assoc, int _zassoc, ReplacementPolicy<T>* _rp, int _hashType)
    : rp(_rp), hf(_hf), numLines(_numLines), ways(_ways), cands(_candidates)
{
    assert_msg(ways > 1, "zcaches need >=2 ways to work");
    assert_msg(cands >= ways, "candidates < ways does not make sense in a zcache");
    assert_msg(numLines % ways == 0, "number of lines is not a multiple of ways");

    //Populate secondary parameters
    numSets = numLines/ways;
    assert_msg(isPow2(numSets), "must have a power of 2 # sets, but you specified %d", numSets);
    setMask = numSets - 1;

    lookupArray = gm_calloc<uint32_t>(numLines);
    array = gm_calloc<Address>(numLines);
    for (uint32_t i = 0; i < numLines; i++) {
        lookupArray[i] = i;  // start with a linear mapping; with swaps, it'll get progressively scrambled
    }
    swapArray = gm_calloc<uint32_t>(cands/ways + 2);  // conservative upper bound (tight within 2 ways)
}

void ZArray::initStats(AggregateStat* parentStat) {
    AggregateStat* objStats = new AggregateStat();
    objStats->init("array", "ZArray stats");
    statSwaps.init("swaps", "Block swaps in replacement process");
    objStats->append(&statSwaps);
    parentStat->append(objStats);
}

int32_t ZArray::lookup(const Address lineAddr, const MemReq* req, bool updateReplacement, uint32_t& secondSearch) {
    /* Be defensive: If the line is 0, panic instead of asserting. Now this can
     * only happen on a segfault in the main program, but when we move to full
     * system, phy page 0 might be used, and this will hit us in a very subtle
     * way if we don't check.
     */
    if (unlikely(!lineAddr)) panic("ZArray::lookup called with lineAddr==0 -- your app just segfaulted");

    for (uint32_t w = 0; w < ways; w++) {
        uint32_t lineId = lookupArray[w*numSets + (hf->hash(w, lineAddr) & setMask)];
        if (array[lineId] == lineAddr) {
            if (updateReplacement) {
                rp->update(lineId, req);
            }
            return lineId;
        }
    }
    return -1;
}

uint32_t ZArray::preinsert(const Address lineAddr, const MemReq* req, Address* wbLineAddr,Address* firstAddr,uint32_t& candidate_2,bool& sec) {
    ZWalkInfo candidates[cands + ways]; //extra ways entries to avoid checking on every expansion

    bool all_valid = true;
    uint32_t fringeStart = 0;
    uint32_t numCandidates = ways; //seeds

    //info("Replacement for incoming 0x%lx", lineAddr);

    //Seeds
    for (uint32_t w = 0; w < ways; w++) {
        uint32_t pos = w*numSets + (hf->hash(w, lineAddr) & setMask);
        uint32_t lineId = lookupArray[pos];
        candidates[w].set(pos, lineId, -1);
        all_valid &= (array[lineId] != 0);
        //info("Seed Candidate %d addr 0x%lx pos %d lineId %d", w, array[lineId], pos, lineId);
    }

    //Expand fringe in BFS fashion
    while (numCandidates < cands && all_valid) {
        uint32_t fringeId = candidates[fringeStart].lineId;
        Address fringeAddr = array[fringeId];
        assert(fringeAddr);
        for (uint32_t w = 0; w < ways; w++) {
            uint32_t hval = hf->hash(w, fringeAddr) & setMask;
            uint32_t pos = w*numSets + hval;
            uint32_t lineId = lookupArray[pos];

            // Logically, you want to do this...
#if 0
            if (lineId != fringeId) {
                //info("Candidate %d way %d addr 0x%lx pos %d lineId %d parent %d", numCandidates, w, array[lineId], pos, lineId, fringeStart);
                candidates[numCandidates++].set(pos, lineId, (int32_t)fringeStart);
                all_valid &= (array[lineId] != 0);
            }
#endif
            // But this compiles as a branch and ILP sucks (this data-dependent branch is long-latency and mispredicted often)
            // Logically though, this is just checking for whether we're revisiting ourselves, so we can eliminate the branch as follows:
            candidates[numCandidates].set(pos, lineId, (int32_t)fringeStart);
            all_valid &= (array[lineId] != 0);  // no problem, if lineId == fringeId the line's already valid, so no harm done
            numCandidates += (lineId != fringeId); // if lineId == fringeId, the cand we just wrote will be overwritten
        }
        fringeStart++;
    }

    //Get best candidate (NOTE: This could be folded in the code above, but it's messy since we can expand more than zassoc elements)
    assert(!all_valid || numCandidates >= cands);
    numCandidates = (numCandidates > cands)? cands : numCandidates;

    //info("Using %d candidates, all_valid=%d", numCandidates, all_valid);

    uint32_t bestCandidate = rp->rankCands(req, ZCands(&candidates[0], &candidates[numCandidates]));
    assert(bestCandidate < numLines);

    //Fill in swap array

    //Get the *minimum* index of cands that matches lineId. We need the minimum in case there are loops (rare, but possible)
    uint32_t minIdx = -1;
    for (uint32_t ii = 0; ii < numCandidates; ii++) {
        if (bestCandidate == candidates[ii].lineId) {
            minIdx = ii;
            break;
        }
    }
    assert(minIdx >= 0);
    //info("Best candidate is %d lineId %d", minIdx, bestCandidate);

    lastCandIdx = minIdx; //used by timing simulation code to schedule array accesses

    int32_t idx = minIdx;
    uint32_t swapIdx = 0;
    while (idx >= 0) {
        swapArray[swapIdx++] = candidates[idx].pos;
        idx = candidates[idx].parentIdx;
    }
    swapArrayLen = swapIdx;
    assert(swapArrayLen > 0);

    //Write address of line we're replacing
    *wbLineAddr = array[bestCandidate];

    return bestCandidate;
}

void ZArray::postinsert(const Address lineAddr, const MemReq* req, uint32_t candidate) {
    //We do the swaps in lookupArray, the array stays the same
    assert(lookupArray[swapArray[0]] == candidate);
    for (uint32_t i = 0; i < swapArrayLen-1; i++) {
        //info("Moving position %d (lineId %d) <- %d (lineId %d)", swapArray[i], lookupArray[swapArray[i]], swapArray[i+1], lookupArray[swapArray[i+1]]);
        lookupArray[swapArray[i]] = lookupArray[swapArray[i+1]];
    }
    lookupArray[swapArray[swapArrayLen-1]] = candidate; //note that in preinsert() we walk the array backwards when populating swapArray, so the last elem is where the new line goes
    //info("Inserting lineId %d in position %d", candidate, swapArray[swapArrayLen-1]);

    rp->replaced(candidate);
    array[candidate] = lineAddr;
    rp->update(candidate, req);

    statSwaps.inc(swapArrayLen-1);
}
