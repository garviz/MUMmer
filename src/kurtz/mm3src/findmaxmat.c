/*
  Copyright (c) 2003 by Stefan Kurtz and The Institute for
  Genomic Research.  This is OSI Certified Open Source Software.
  Please see the file LICENSE for licensing information and
  the file ACKNOWLEDGEMENTS for names of contributors to the
  code base.
*/

//\IgnoreLatex{

#include <stdio.h>
#include <ctype.h>
#include <vector>
#include <iostream>
#include "streedef.h"
#include "debugdef.h"
#include "spacedef.h"
#include "maxmatdef.h"
#include "streeacc.h"
#include "streehuge.h"
#include "protodef.h"
#include "types.h"
#include "intbits.h"
#include "visible.h"
#include "arraydef.h"

//}

using namespace std;
/*EE
  This file contains functions to compute maximal matches of some
  minimum length between the subject-sequence and the query-sequence.
  This is done by a traversal of the suffix tree of the subject-sequence.
  For each suffix, say \(s\), of the query, the location \texttt{ploc}
  of some prefix \(p\) of \(s\) is determined. 
  Let \texttt{pmax} be the longest prefix
  of \(s\) that occurs as a substring of the subject-sequence.
  \(p\) is determined as follows.
  \begin{itemize}
  \item
  If the length of \texttt{pmax} is \(\leq\mathtt{minmatchlength}\), 
  then \(p=\texttt{pmax}\).
  \item
  If the length of \texttt{pmax} is \(>\texttt{minmatchlength}\), then
  \(p\) is the prefix of \texttt{pmax} of length 
  \(\texttt{minmatchlength}\).
  \end{itemize}
  Given \texttt{ploc}, the location \texttt{maxloc} of \texttt{pmax} is 
  determined, thereby keeping track of the branching nodes 
  visited during this matching
  step. Finally, the suffix tree below location \texttt{ploc}
  is traversed
  in a depth first strategy. This delivers the set of suffixes representing
  a match of length at least \(\texttt{minmatchlength}\) against 
  a prefix of \(s\).
  Using a stack one keeps track of the length of the longest common prefix 
  of each encountered suffix and \(s\). Finally, it is checked whether the
  match between the match is maximal by comparing the characters
  to the left and to the right of the two instances of the match.
*/

/*EE
  For the depth first traversal we need a stack containing elements
  of the following type. Each stack element stores information for
  a branching node of the suffix tree. The top of the stack corresponds
  to the branching node, say \(b\), currently visited.
  \texttt{querycommondepth} is the length of the longest common prefix
  of \(s\) and all suffixes represented by leaves in the subtree below 
  \(b\). \texttt{onmaxpath} is \texttt{true} iff the sequence 
  corresponding to \(b\) is a prefix of the query.
*/

typedef struct
{
  Uint querycommondepth;
  BOOL onmaxpath;
} Nodeinfo;

/*EE
  The stack is represented by a dynamic array of elements of type 
  \texttt{Nodeinfo}.
*/

DECLAREARRAYSTRUCT(Nodeinfo);

/*EE
  The following type contains all information required during the
  computation of the maximal matches.
*/

typedef struct
{
  Suffixtree *stree;              // reference to suffix tree of subject-seq
  ArrayNodeinfo commondepthstack; // stack to store depth values
  ArrayPathinfo matchpath;        // path of br. nodes from ploc to maxloc
  Location maxloc;                // location of \texttt{pmax}
  Uchar *query,                   // the query string
        *querysuffix;             // current suffix of query
  Uint querylen,                  // length of the current query
       queryseqnum,               // number of query sequence
       minmatchlength,            // min length of a match to be reported
       depthofpreviousmaxloc;     // the depth of the previous maxloc
  Processmatchfunction processmatch; // this function processes found match
  void *processinfo;            // first arg. when calling previous function
} Maxmatchinfo;

//\IgnoreLatex{

#define CHECKIFLOCATIONISVALID(LOC) /* Nothing */

#define SETCURRENT(V)\
        if(ISLEAF(V))\
        {\
          currentnode.address = stree->leaftab + GETLEAFINDEX(V);\
          currentnode.toleaf = True;\
        } else\
        {\
          currentnode.address = stree->branchtab + GETBRANCHINDEX(V);\
          currentnode.toleaf = False;\
        }
//}

Sint depthfirststree(Suffixtree *stree,Reference *startnode,
                     Sint (*processleaf)(Uint,Bref,void *),
                     BOOL (*processbranch1)(Bref,void *),
                     Sint (*processbranch2)(Bref,void *),
                     BOOL (*stoptraversal)(void *),void *stopinfo,void *info)
{
  BOOL godown = True, readyforpop = False;
  Uint child, brotherval;
  Bref lcpnode = NULL;
  Reference currentnode;
  ArrayBref stack;

  if(startnode->toleaf)
  {
    if(processleaf((Uint) (startnode->address - stree->leaftab),NULL,info) != 0)
    {
      return -1;
    }
    return 0;
  }
  if(stoptraversal != NULL && stoptraversal(stopinfo))
  {
    return 0;
  }

  currentnode.toleaf = False;
  currentnode.address = startnode->address;
  INITARRAY(&stack,Bref);
  STOREINARRAY(&stack,Bref,128,currentnode.address);
  SETCURRENT(GETCHILD(currentnode.address));

  if(processbranch1 == NULL)
  {
#define PROCESSBRANCH1(A,B) /* Nothing */
#define PROCESSBRANCH2(A,B) godown = True
#include "dfs.gen"
  } else
  {
#undef PROCESSBRANCH1
#undef PROCESSBRANCH2
#define PROCESSBRANCH1(A,B) godown = processbranch1(A,B)
#define PROCESSBRANCH2(A,B) if(processbranch2(A,B) != 0)\
                            {\
                              return -2;\
                            }
#include "dfs.gen"
  }
  FREEARRAY(&stack,Bref);
  return 0;
}

static void int2ref(Suffixtree *stree,Reference *ref,Uint i)
{
  if(ISLEAF(i))
  {
    ref->toleaf = True;
    ref->address = stree->leaftab + GETLEAFINDEX(i);
  } else
  {
    ref->toleaf = False;
    ref->address = stree->branchtab + GETBRANCHINDEX(i);
  }
}

static Uint getlargelinkstree(/*@unused@*/ Suffixtree *stree,Bref btptr,Uint depth)
{
  if(depth == UintConst(1))
  {
    return 0;
  }
  return *(btptr+4);
}

static void rescanstree(Suffixtree *stree,Location *loc,
                 Bref btptr,SYMBOL *left,SYMBOL *right)
{
  Uint *nodeptr, *largeptr = NULL, leafindex, nodedepth, 
       node, distance = 0, prefixlen, headposition, tmpnodedepth;
  SYMBOL *lptr;

  lptr = left;
  nodeptr = btptr; 
  if(nodeptr == stree->branchtab)
  {
    nodedepth = 0;
    headposition = 0;
  } else
  {
    GETBOTH(nodedepth,headposition,nodeptr);
  }
  loc->nextnode.toleaf = False;
  loc->nextnode.address = nodeptr;
  loc->locstring.start = headposition;
  loc->locstring.length = nodedepth;
  loc->remain = 0;
  while(True)
  {
    if(lptr > right)   // check for empty word
    {
      return;
    }
    if(nodeptr == stree->branchtab)  // at the root
    {
      node = stree->rootchildren[(Uint) *lptr];
      prefixlen = (Uint) (right - lptr + 1);
      if(ISLEAF(node))   // stop if successor is leaf
      {
        leafindex = GETLEAFINDEX(node);
        loc->firstptr = stree->text + leafindex;
        loc->previousnode = stree->branchtab;
        loc->edgelen = stree->textlen - leafindex + 1;
        loc->remain = loc->edgelen - prefixlen;
        loc->nextnode.toleaf = True;
        loc->nextnode.address = stree->leaftab + leafindex;
        loc->locstring.start = leafindex;
        loc->locstring.length = prefixlen;
        return;
      } 
      nodeptr = stree->branchtab + GETBRANCHINDEX(node);
      GETONLYHEADPOS(headposition,nodeptr);
      loc->firstptr = stree->text + headposition;
    } else
    {
      node = GETCHILD(nodeptr);
      while(True)             // traverse the list of successors
      {
        if(ISLEAF(node))   // successor is leaf
        {
          leafindex = GETLEAFINDEX(node);
          loc->firstptr = stree->text + (nodedepth + leafindex);
          if(*(loc->firstptr) == *lptr)    // correct edge found
          {
            prefixlen = (Uint) (right - lptr + 1);
            loc->previousnode = loc->nextnode.address;
            loc->edgelen = stree->textlen - (nodedepth + leafindex) + 1;
            loc->remain = loc->edgelen - prefixlen;
            loc->nextnode.toleaf = True;
            loc->nextnode.address = stree->leaftab + leafindex;
            loc->locstring.start = leafindex;
            loc->locstring.length = nodedepth + prefixlen;
            return;
          }
          node = LEAFBROTHERVAL(stree->leaftab[leafindex]);  
        } else   // successor is branch node
        {
          nodeptr = stree->branchtab + GETBRANCHINDEX(node);
          GETONLYHEADPOS(headposition,nodeptr);
          loc->firstptr = stree->text + (nodedepth + headposition);
          if(*(loc->firstptr) == *lptr) // correct edge found
          {
            /*@innerbreak@*/ break;
          } 
          node = GETBROTHER(nodeptr);
        }
      }
    }
    GETONLYDEPTH(tmpnodedepth,nodeptr);     // get info about succ node
    loc->edgelen = tmpnodedepth - nodedepth;
    prefixlen = (Uint) (right - lptr + 1);
    loc->previousnode = loc->nextnode.address;
    loc->nextnode.toleaf = False;
    loc->nextnode.address = nodeptr;
    loc->locstring.start = headposition;
    loc->locstring.length = nodedepth + prefixlen;
    if(loc->edgelen > prefixlen)     // can reach the successor node
    {
      loc->remain = loc->edgelen - prefixlen;
      return;
    } 
    if(loc->edgelen == prefixlen)
    {
      loc->remain = 0;
      return;
    }
    lptr += loc->edgelen;
    nodedepth = tmpnodedepth;
  }
}

static void getbranchinfostree(Suffixtree *stree,Uint whichinfo,
                        Branchinfo *branchinfo,Bref btptr)
{
  Uint which = whichinfo, node, distance, *largeptr;

  if(which & ACCESSSUFFIXLINK)
  {
    which |= ACCESSDEPTH;
  }
  if(which & (ACCESSDEPTH | ACCESSHEADPOS))
  {
    if(stree->chainstart != NULL && btptr >= stree->chainstart)
    {
      distance = DIVBYSMALLINTS((Uint) (stree->nextfreebranch - btptr));
      branchinfo->depth = stree->currentdepth + distance;
      branchinfo->headposition = stree->nextfreeleafnum - distance;
    } else
    {
      if(ISLARGE(*btptr))
      {
        if(which & ACCESSDEPTH)
        {
          branchinfo->depth = GETDEPTH(btptr);
        }
        if(which & ACCESSHEADPOS)
        {
          branchinfo->headposition = GETHEADPOS(btptr);
        }
      } else
      {
        distance = GETDISTANCE(btptr);
        GETCHAINEND(largeptr,btptr,distance);
        if(which & ACCESSDEPTH)
        {
          branchinfo->depth = GETDEPTH(largeptr) + distance;
        }
        if(which & ACCESSHEADPOS)
        {
          branchinfo->headposition = GETHEADPOS(largeptr) - distance;
        }
      }
    }
  }
  if(which & ACCESSSUFFIXLINK)
  {
    if((stree->chainstart != NULL && btptr >= stree->chainstart) || 
       !ISLARGE(*btptr))
    {
      branchinfo->suffixlink = btptr + SMALLINTS;
    } else
    {
      branchinfo->suffixlink = stree->branchtab + 
                               getlargelinkstree(stree,btptr,
                                                 branchinfo->depth);
    }
  }
  if(which & ACCESSFIRSTCHILD)
  {
    int2ref(stree,&(branchinfo->firstchild),GETCHILD(btptr));
  }
  if(which & ACCESSBRANCHBROTHER)
  {
    node = GETBROTHER(btptr);
    if(NILPTR(node))
    {
      branchinfo->branchbrother.address = NULL;
    } else
    {
      int2ref(stree,&(branchinfo->branchbrother),node);
    }
  }
}

static Uint lcp(SYMBOL *start1,SYMBOL *end1,SYMBOL *start2,SYMBOL *end2)
{
  register SYMBOL *ptr1 = start1, 
                  *ptr2 = start2;

  while(ptr1 <= end1 && 
        ptr2 <= end2 &&
        *ptr1 == *ptr2)
  {
    ptr1++;
    ptr2++;
  }
  return (Uint) (ptr1-start1);
}

static /*@null@*/ SYMBOL *scanprefixfromnodestree(Suffixtree *stree,Location *loc,
                                           Bref btptr,SYMBOL *left,
                                           SYMBOL *right,Uint rescanlength)
{
  Uint *nodeptr = NULL, *largeptr = NULL, leafindex, nodedepth, 
       node, distance = 0, prefixlen, headposition, tmpnodedepth,
       edgelen, remainingtoskip;
  SYMBOL *lptr, *leftborder = (SYMBOL *) NULL, firstchar, edgechar = 0;

  lptr = left;
  nodeptr = btptr;
  if(nodeptr == stree->branchtab)
  {
    nodedepth = 0;
    headposition = 0;
  } else
  {
    GETBOTH(nodedepth,headposition,nodeptr);
  }
  loc->nextnode.toleaf = False;
  loc->nextnode.address = nodeptr;
  loc->locstring.start = headposition;
  loc->locstring.length = nodedepth;
  loc->remain = 0;
  if(rescanlength <= nodedepth)
  {
    remainingtoskip = 0;
  } else
  {
    remainingtoskip = rescanlength - nodedepth;
  }
  while(True)
  {
    if(lptr > right)   // check for empty word
    {
      return NULL;
    }
    firstchar = *lptr;
    if(nodeptr == stree->branchtab)  // at the root
    {
      if((node = stree->rootchildren[(Uint) firstchar]) == UNDEFINEDREFERENCE)
      {
        return lptr;
      }
      if(ISLEAF(node))
      {
        leafindex = GETLEAFINDEX(node);
        loc->firstptr = stree->text + leafindex;
        if(remainingtoskip > 0)
        {
          prefixlen = remainingtoskip + 
                      lcp(lptr+remainingtoskip,right,
                          loc->firstptr+remainingtoskip,stree->sentinel-1);
        } else
        {
          prefixlen = 1 + lcp(lptr+1,right,
                              loc->firstptr+1,stree->sentinel-1);
        }
        loc->previousnode = stree->branchtab;
        loc->edgelen = stree->textlen - leafindex + 1;
        loc->remain = loc->edgelen - prefixlen;
        loc->nextnode.toleaf = True;
        loc->nextnode.address = stree->leaftab + leafindex;
        loc->locstring.start = leafindex;
        loc->locstring.length = prefixlen;
        if(prefixlen == (Uint) (right - lptr + 1))
        {
          return NULL;
        }
        return lptr + prefixlen;
      } 
      nodeptr = stree->branchtab + GETBRANCHINDEX(node);
      GETONLYHEADPOS(headposition,nodeptr);
      leftborder = stree->text + headposition;
    } else
    {
      node = GETCHILD(nodeptr);
      while(True)
      {
        if(NILPTR(node))
        {
          return lptr;
        }
        if(ISLEAF(node))
        {
          leafindex = GETLEAFINDEX(node);
          leftborder = stree->text + (nodedepth + leafindex);
          if(leftborder == stree->sentinel)
          {
            return lptr;
          }
          edgechar = *leftborder;
          if(edgechar > firstchar)
          {
            return lptr;
          }
          if(edgechar == firstchar)
          {
            if(remainingtoskip > 0)
            {
              prefixlen = remainingtoskip +
                          lcp(lptr+remainingtoskip,right,
                              leftborder+remainingtoskip,stree->sentinel-1);
            } else
            {
              prefixlen = 1 + lcp(lptr+1,right,
                                  leftborder+1,stree->sentinel-1);
            }
            loc->firstptr = leftborder;
            loc->previousnode = loc->nextnode.address;
            loc->edgelen = stree->textlen - (nodedepth + leafindex) + 1;
            loc->remain = loc->edgelen - prefixlen;
            loc->nextnode.toleaf = True;
            loc->nextnode.address = stree->leaftab + leafindex;
            loc->locstring.start = leafindex;
            loc->locstring.length = nodedepth + prefixlen;
            if(prefixlen == (Uint) (right - lptr + 1))
            {
              return NULL;
            }
            return lptr + prefixlen;
          }
          node = LEAFBROTHERVAL(stree->leaftab[leafindex]);
        } else
        {
          nodeptr = stree->branchtab + GETBRANCHINDEX(node);
          GETONLYHEADPOS(headposition,nodeptr);
          leftborder = stree->text + (nodedepth + headposition);
          edgechar = *leftborder;
          if (edgechar > firstchar)
          {
            return lptr;
          }
          if(edgechar == firstchar)
          {
            /*@innerbreak@*/ break;
          }
          node = GETBROTHER(nodeptr);
        }
      }
    }
    GETONLYDEPTH(tmpnodedepth,nodeptr);
    edgelen = tmpnodedepth - nodedepth;
    if(remainingtoskip > 0)
    {
      if(remainingtoskip >= edgelen)
      {
        prefixlen = edgelen;
        remainingtoskip -= prefixlen;
      } else
      {
        NOTSUPPOSEDTOBENULL(leftborder);
        prefixlen = remainingtoskip + 
                    lcp(lptr+remainingtoskip,right,
                        leftborder+remainingtoskip,leftborder+edgelen-1);
        remainingtoskip = 0;
      }
    } else
    {
      NOTSUPPOSEDTOBENULL(leftborder);
      prefixlen = 1 + lcp(lptr+1,right,
                          leftborder+1,leftborder+edgelen-1);
    }
    loc->nextnode.toleaf = False;
    loc->locstring.start = headposition;
    loc->locstring.length = nodedepth + prefixlen;
    if(prefixlen == edgelen)
    {
      lptr += edgelen;
      nodedepth += edgelen;
      loc->nextnode.address = nodeptr;
      loc->remain = 0;
    } else
    {
      loc->firstptr = leftborder;
      loc->previousnode = loc->nextnode.address;
      loc->nextnode.address = nodeptr;
      loc->edgelen = edgelen;
      loc->remain = loc->edgelen - prefixlen;
      if(prefixlen == (Uint) (right - lptr + 1))
      {
        return NULL;
      }
      return lptr + prefixlen;
    }
  }
}

static void linklocstree(Suffixtree *stree,Location *outloc,Location *inloc)
{
  Branchinfo branchinfo;

  if(inloc->remain == 0)
  {
    outloc->remain = 0;
    outloc->nextnode.toleaf = False;
    getbranchinfostree(stree,ACCESSSUFFIXLINK,&branchinfo,
                       inloc->nextnode.address);
    outloc->nextnode.address = branchinfo.suffixlink;
    outloc->locstring.start = inloc->locstring.start + 1;
    outloc->locstring.length = inloc->locstring.length - 1;
  } else
  {
    if(inloc->previousnode == stree->branchtab)
    {
      rescanstree(stree,outloc,stree->branchtab,inloc->firstptr+1,
                  inloc->firstptr + (inloc->edgelen - inloc->remain) - 1);
    } else
    {
      getbranchinfostree(stree,ACCESSSUFFIXLINK,&branchinfo,
                         inloc->previousnode);
      rescanstree(stree,outloc,branchinfo.suffixlink,inloc->firstptr,
             inloc->firstptr + (inloc->edgelen - inloc->remain) - 1);
      
    }
  } 
}

static /*@null@*/ SYMBOL *scanprefixstree(Suffixtree *stree,Location *outloc,
                                   Location *inloc,SYMBOL *left,
                                   SYMBOL *right,Uint rescanlength)
{
  Uint prefixlen, remainingtoskip;

  DEBUG0(4,"scanprefixstree starts at location ");
  //DEBUGCODE(4,showlocation(stdout,stree,inloc));
  DEBUG0(4,"\n");
  if(inloc->remain == 0)
  {
    return scanprefixfromnodestree(stree,outloc,inloc->nextnode.address,
                                   left,right,rescanlength);
  } 
  if(rescanlength <= inloc->locstring.length)
  {
    remainingtoskip = 0;
  } else
  {
    remainingtoskip = rescanlength - inloc->locstring.length;
  }
  if(inloc->nextnode.toleaf)
  {
    
    if(remainingtoskip > 0)
    {
      prefixlen = remainingtoskip +
                  lcp(left+remainingtoskip,right,
                      inloc->firstptr+(inloc->edgelen-inloc->remain)
                                     +remainingtoskip,
                      stree->sentinel-1);
    } else
    {
      prefixlen = lcp(left,right,
                      inloc->firstptr+(inloc->edgelen-inloc->remain),
                      stree->sentinel-1);
    }
    outloc->firstptr = inloc->firstptr;
    outloc->edgelen = inloc->edgelen;
    outloc->remain = inloc->remain - prefixlen;
    outloc->previousnode = inloc->previousnode;
    outloc->nextnode.toleaf = True;
    outloc->nextnode.address = inloc->nextnode.address;
    outloc->locstring.start = LEAFADDR2NUM(stree,inloc->nextnode.address);
    outloc->locstring.length = inloc->locstring.length + prefixlen;
    return left + prefixlen;
  }
  if(remainingtoskip > 0)
  {
    if(remainingtoskip >= inloc->remain)
    {
      prefixlen = inloc->remain;
    } else
    {
      prefixlen = remainingtoskip + 
                  lcp(left+remainingtoskip,right,
                      inloc->firstptr+(inloc->edgelen-inloc->remain)
                                     +remainingtoskip,
                      inloc->firstptr+inloc->edgelen-1);
    }
  } else
  {
    prefixlen = lcp(left,right,
                    inloc->firstptr+(inloc->edgelen-inloc->remain),
                    inloc->firstptr+inloc->edgelen-1);
  }
  if(prefixlen < inloc->remain)
  {
    outloc->firstptr = inloc->firstptr;
    outloc->edgelen = inloc->edgelen;
    outloc->remain = inloc->remain - prefixlen;
    outloc->previousnode = inloc->previousnode;
    outloc->nextnode.toleaf = False;
    outloc->nextnode.address = inloc->nextnode.address;
    outloc->locstring.start = inloc->locstring.start;
    outloc->locstring.length = inloc->locstring.length + prefixlen;
    return left + prefixlen;
  }
  return scanprefixfromnodestree(stree,outloc,inloc->nextnode.address,
                                   left+prefixlen,right,rescanlength);
}

/*@null@*/SYMBOL *findprefixpathfromnodestree(Suffixtree *stree,
                                              ArrayPathinfo *path,
                                              Location *loc,
                                              Bref btptr,
                                              SYMBOL *left,
                                              SYMBOL *right,
                                              Uint rescanlength)
{
  Uint *nodeptr = NULL, *largeptr = NULL, leafindex, nodedepth, 
       edgelen, node, distance = 0, prefixlen, headposition, 
       remainingtoskip, tmpnodedepth;
  SYMBOL *leftborder = (SYMBOL *) NULL, *lptr, firstchar, edgechar = 0;

  lptr = left;
  nodeptr = btptr;
  if(nodeptr == stree->branchtab)
  {
    nodedepth = 0;
    headposition = 0;
  } else
  {
    GETBOTH(nodedepth,headposition,nodeptr);
  }
  loc->nextnode.toleaf = False;
  loc->nextnode.address = nodeptr;
  loc->locstring.start = headposition;
  loc->locstring.length = nodedepth;
  loc->remain = 0;
  if(rescanlength <= nodedepth)
  {
    remainingtoskip = 0;
  } else
  {
    remainingtoskip = rescanlength - nodedepth;
  }
  while(True)
  {
    if(lptr > right)   // check for empty word
    {
      return NULL;
    }
    firstchar = *lptr;
    if(nodeptr == stree->branchtab)  // at the root
    {
      if((node = stree->rootchildren[(Uint) firstchar]) == UNDEFINEDREFERENCE)
      {
        return lptr;
      }
      if(ISLEAF(node))
      {
        leafindex = GETLEAFINDEX(node);
        loc->firstptr = stree->text + leafindex;
        if(remainingtoskip > 0)
        {
          prefixlen = remainingtoskip +
                      lcp(lptr+remainingtoskip,right,
                          loc->firstptr+remainingtoskip,stree->sentinel-1);
        } else
        {
          prefixlen = 1 + lcp(lptr+1,right,
                              loc->firstptr+1,stree->sentinel-1);
        }
        loc->previousnode = stree->branchtab;
        loc->edgelen = stree->textlen - leafindex + 1;
        loc->remain = loc->edgelen - prefixlen;
        loc->nextnode.toleaf = True;
        loc->nextnode.address = stree->leaftab + leafindex;
        loc->locstring.start = leafindex;
        loc->locstring.length = prefixlen;
        if(prefixlen == (Uint) (right - lptr + 1))
        {
          return NULL;
        }
        return lptr + prefixlen;
      } 
      nodeptr = stree->branchtab + GETBRANCHINDEX(node);
      GETONLYHEADPOS(headposition,nodeptr);
      leftborder = stree->text + headposition;
    } else
    {
      node = GETCHILD(nodeptr);
      while(True)
      {
        if(NILPTR(node))
        {
          return lptr;
        }
        if(ISLEAF(node))
        {
          leafindex = GETLEAFINDEX(node);
          leftborder = stree->text + (nodedepth + leafindex);
          if(leftborder == stree->sentinel)
          {
            return lptr;
          }
          edgechar = *leftborder;
          if(edgechar > firstchar)
          {
            return lptr;
          }
          if(edgechar == firstchar)
          {
            if(remainingtoskip > 0)
            {
              prefixlen = remainingtoskip +
                          lcp(lptr+remainingtoskip,right,
                              leftborder+remainingtoskip,stree->sentinel-1);
            } else
            {
              prefixlen = 1 + lcp(lptr+1,right,
                                  leftborder+1,stree->sentinel-1);
            }
            loc->firstptr = leftborder;
            loc->previousnode = loc->nextnode.address;
            loc->edgelen = stree->textlen - (nodedepth + leafindex) + 1;
            loc->remain = loc->edgelen - prefixlen;
            loc->nextnode.toleaf = True;
            loc->nextnode.address = stree->leaftab + leafindex;
            loc->locstring.start = leafindex;
            loc->locstring.length = nodedepth + prefixlen;
            if(prefixlen == (Uint) (right - lptr + 1))
            {
              return NULL;
            }
            return lptr + prefixlen;
          }
          node = LEAFBROTHERVAL(stree->leaftab[leafindex]);
        } else
        {
          nodeptr = stree->branchtab + GETBRANCHINDEX(node);
          GETONLYHEADPOS(headposition,nodeptr);
          leftborder = stree->text + (nodedepth + headposition);
          edgechar = *leftborder;
          if (edgechar > firstchar)
          {
            return lptr;
          }
          if(edgechar == firstchar)
          {
            /*@innerbreak@*/ break;
          }
          node = GETBROTHER(nodeptr);
        }
      }
    }
    GETONLYDEPTH(tmpnodedepth,nodeptr);
    edgelen = tmpnodedepth - nodedepth;
    if(remainingtoskip > 0)
    {
      if(remainingtoskip >= edgelen)
      {
        prefixlen = edgelen;
        remainingtoskip -= prefixlen;
      } else
      {
        NOTSUPPOSEDTOBENULL(leftborder);
        prefixlen = remainingtoskip +
                    lcp(lptr+remainingtoskip,right,
                        leftborder+remainingtoskip,leftborder+edgelen-1);
        remainingtoskip = 0;
      }
    } else
    {
      NOTSUPPOSEDTOBENULL(leftborder);
      prefixlen = 1 + lcp(lptr+1,right,
                          leftborder+1,leftborder+edgelen-1);
    }
    loc->nextnode.toleaf = False;
    loc->locstring.start = headposition;
    loc->locstring.length = nodedepth + prefixlen;
    if(prefixlen == edgelen)
    {
      lptr += edgelen;
      nodedepth += edgelen;
      loc->nextnode.address = nodeptr;
      loc->remain = 0;
    } else
    {
      loc->firstptr = leftborder;
      loc->previousnode = loc->nextnode.address;
      loc->nextnode.address = nodeptr;
      loc->edgelen = edgelen;
      loc->remain = loc->edgelen - prefixlen;
      if(prefixlen == (Uint) (right - lptr + 1))
      {
        return NULL;
      }
      return lptr + prefixlen;
    }
    CHECKARRAYSPACE(path,Pathinfo,128);
    path->spacePathinfo[path->nextfreePathinfo].ref = nodeptr;
    path->spacePathinfo[path->nextfreePathinfo].depth = tmpnodedepth;
    path->spacePathinfo[path->nextfreePathinfo].headposition = headposition;
    path->nextfreePathinfo++;
  }
}

/*@null@*/ SYMBOL *findprefixpathstree(Suffixtree *stree,
                                       ArrayPathinfo *path,
                                       Location *outloc,
                                       Location *inloc,
                                       SYMBOL *left,
                                       SYMBOL *right,
                                       Uint rescanlength)
{
  Uint prefixlen, remainingtoskip;

  DEBUG0(4,"findprefixpathstree starts at location ");
  //DEBUGCODE(4,showlocation(stdout,stree,inloc));
  DEBUG0(4,"\n");
  if(inloc->remain == 0)
  {
    CHECKARRAYSPACE(path,Pathinfo,128);
    path->spacePathinfo[path->nextfreePathinfo].ref 
      = inloc->nextnode.address;
    path->spacePathinfo[path->nextfreePathinfo].depth 
      = inloc->locstring.length;
    path->spacePathinfo[path->nextfreePathinfo].headposition 
      = inloc->locstring.start;
    path->nextfreePathinfo++;
    return findprefixpathfromnodestree(stree,path,outloc,
                                       inloc->nextnode.address,
                                       left,right,rescanlength);
  } 
  if(rescanlength <= inloc->locstring.length)
  {
    remainingtoskip = 0;
  } else
  {
    remainingtoskip = rescanlength - inloc->locstring.length;
  }
  if(inloc->nextnode.toleaf)
  {
    if(remainingtoskip > 0)
    {
      prefixlen = remainingtoskip +
                  lcp(left+remainingtoskip,right,
                      inloc->firstptr+(inloc->edgelen-inloc->remain)
                                     +remainingtoskip,
                      stree->sentinel-1);
    } else
    {
      prefixlen = lcp(left,right,
                      inloc->firstptr+(inloc->edgelen-inloc->remain),
                      stree->sentinel-1);
    }
    outloc->firstptr = inloc->firstptr;
    outloc->edgelen = inloc->edgelen;
    outloc->remain = inloc->remain - prefixlen;
    outloc->previousnode = inloc->previousnode;
    outloc->nextnode.toleaf = True;
    outloc->nextnode.address = inloc->nextnode.address;
    outloc->locstring.start = LEAFADDR2NUM(stree,inloc->nextnode.address);
    outloc->locstring.length = inloc->locstring.length + prefixlen;
    return left + prefixlen;
  }
  if(remainingtoskip > 0)
  {
    if(remainingtoskip >= inloc->remain)
    {
      prefixlen = inloc->remain;
    } else
    {
      prefixlen = remainingtoskip +
                  lcp(left+remainingtoskip,right,
                      inloc->firstptr+(inloc->edgelen-inloc->remain)
                                     +remainingtoskip,
                      inloc->firstptr+inloc->edgelen-1);
    }
  } else
  {
    prefixlen = lcp(left,right,
                    inloc->firstptr+(inloc->edgelen-inloc->remain),
                    inloc->firstptr+inloc->edgelen-1);
  }
  if(prefixlen < inloc->remain)
  {
    outloc->firstptr = inloc->firstptr;
    outloc->edgelen = inloc->edgelen;
    outloc->remain = inloc->remain - prefixlen;
    outloc->previousnode = inloc->previousnode;
    outloc->nextnode.toleaf = False;
    outloc->nextnode.address = inloc->nextnode.address;
    outloc->locstring.start = inloc->locstring.start;
    outloc->locstring.length = inloc->locstring.length + prefixlen;
    return left + prefixlen;
  }
  CHECKARRAYSPACE(path,Pathinfo,128);
  path->spacePathinfo[path->nextfreePathinfo].ref = inloc->nextnode.address;
  path->spacePathinfo[path->nextfreePathinfo].depth 
    = inloc->locstring.length + prefixlen;
  path->spacePathinfo[path->nextfreePathinfo].headposition 
      = inloc->locstring.start;
  path->nextfreePathinfo++;
  return findprefixpathfromnodestree(stree,path,outloc,
                                     inloc->nextnode.address,
                                     left+prefixlen,right,rescanlength);
}

/*
  The following function is applied to each leaf visited during
  the depth first traversal. It checks if corresponding match is
  left maximal. In this case, the length of the longest common
  prefix of this suffix and \(s\) is computed.
*/

static Sint processleaf(Uint leafindex,/*@unused@*/ Bref lcpnode,void *info)
{
  Maxmatchinfo *maxmatchinfo = (Maxmatchinfo *) info;

  DEBUG1(2,"processleaf %lu\n",(Showuint) leafindex);
  if(leafindex == 0 ||
     maxmatchinfo->query == maxmatchinfo->querysuffix ||
     maxmatchinfo->stree->text[leafindex - 1] != 
     *(maxmatchinfo->querysuffix-1))
  {
    Uint lcplength;

    if(maxmatchinfo->commondepthstack.nextfreeNodeinfo == 0)
    {
      CHECKIFLOCATIONISVALID(&maxmatchinfo->maxloc);
      lcplength = maxmatchinfo->maxloc.locstring.length;
    } else
    {
      Nodeinfo *father = maxmatchinfo->commondepthstack.spaceNodeinfo + 
                         maxmatchinfo->commondepthstack.nextfreeNodeinfo-1;
      if(father->onmaxpath &&
         LEAFADDR2NUM(maxmatchinfo->stree,
                      maxmatchinfo->maxloc.nextnode.address) == leafindex)
      {
        lcplength = maxmatchinfo->maxloc.locstring.length;
      } else
      {
        lcplength = father->querycommondepth;
      }
    }
    if(maxmatchinfo->processmatch(
                maxmatchinfo->processinfo,
                lcplength,                           // length of match
	        leafindex,                           // dbstart
                maxmatchinfo->queryseqnum,
                (Uint) (maxmatchinfo->querysuffix - 
                        maxmatchinfo->query)) != 0)  // querystart
    {
      return -1;
    }
  }
  return 0;
}

/*
  The following functions inherits information from the maximal matchpath
  to the stack used in the depth first traversal.
*/

static void inheritfrompath(ArrayPathinfo *matchpath,Location *maxloc,
                            Nodeinfo *stacktop,Bref nodeptr,
                            Uint accessindex,
                            Uint inheritdepth)
{
  DEBUG2(2,"inheritfrompath(accessindex=%lu,inheritdepth=%lu)\n",
              (Showuint) accessindex,(Showuint) inheritdepth);
  if(accessindex > matchpath->nextfreePathinfo)
  {
    stacktop->onmaxpath = False;
    stacktop->querycommondepth = inheritdepth;
  } else
  {
    if(accessindex == matchpath->nextfreePathinfo)
    {
      if(maxloc->remain == 0)
      {
        if(maxloc->nextnode.address == nodeptr)
        {
          stacktop->onmaxpath = True;
          stacktop->querycommondepth = maxloc->locstring.length;
        } else
        {
          stacktop->onmaxpath = False;
          stacktop->querycommondepth = inheritdepth;
        }
      } else
      {
        stacktop->onmaxpath = False;
        if(maxloc->nextnode.address == nodeptr)
        {
          stacktop->querycommondepth = maxloc->locstring.length;
        } else
        {
          stacktop->querycommondepth = inheritdepth;
        }
      }
    } else
    {
      if(matchpath->spacePathinfo[accessindex].ref == nodeptr)
      {
        stacktop->onmaxpath = True;
        stacktop->querycommondepth 
          = matchpath->spacePathinfo[accessindex].depth;
      } else
      {
        stacktop->onmaxpath = False;
        stacktop->querycommondepth = inheritdepth;
      }
    }
  }
}

/*
  The following function is called whenever during a depth first traversal
  of a subtree of the suffix tree, each time
  a branching node is visited for the first time.
  The arguments are the branching node \texttt{nodeptr} and 
  a pointer \texttt{info} to some information passed to the function 
  \texttt{depthfirststree}. If the \texttt{commondepthstack}
  is empty or the father of the current node is on the maximal path,
  then the commondepthstack inherits information from the appropriate
  value of the maximal match path. Otherwise, the information about
  the maximal matching prefix length is propagated down the stack.
  The function always return \texttt{True} and thus the depth first
  traversal continues.
*/

static BOOL processbranch1(Bref nodeptr,void *info)
{
  Maxmatchinfo *maxmatchinfo = (Maxmatchinfo *) info;
  Nodeinfo *stacktop, 
           *father;
  GETNEXTFREEINARRAY(stacktop,&maxmatchinfo->commondepthstack,Nodeinfo,32);
  DEBUG1(2,"pushnodeinfo(nodeptr=%lu)\n",
            (Showuint) BRADDR2NUM(maxmatchinfo->stree,nodeptr));
  if(stacktop == maxmatchinfo->commondepthstack.spaceNodeinfo)
  {
    inheritfrompath(&maxmatchinfo->matchpath,
                    &maxmatchinfo->maxloc,
                    stacktop,
                    nodeptr,
                    0,
                    maxmatchinfo->minmatchlength);
  } else
  {
    father = stacktop-1;
    if(father->onmaxpath)
    {
      inheritfrompath(&maxmatchinfo->matchpath,
                      &maxmatchinfo->maxloc,
                      stacktop,
                      nodeptr,
                      maxmatchinfo->commondepthstack.nextfreeNodeinfo-1,
                      father->querycommondepth);
    } else
    {
      stacktop->onmaxpath = False;
      stacktop->querycommondepth = father->querycommondepth;
    }
  }
  return True;
}

/*
  The following function is called whenever a branching node 
  \texttt{nodeptr}
  is visited for the second time (i.e.\ the entire subtree below 
  \texttt{nodeptr} has been processed).
  \texttt{info} is a pointer to some information passed to the function
  \texttt{depthfirststree}.
*/

static Sint processbranch2(/*@unused@*/ Bref nodeptr,void *info)
{
  Maxmatchinfo *maxmatchinfo = (Maxmatchinfo *) info;

  maxmatchinfo->commondepthstack.nextfreeNodeinfo--;
  return 0;
}

/*
  The following function computes the maximal matches below location
  \(ploc\). All global information is passed via the 
  \texttt{Maxmatchinfo}-record. At first the number 
  \texttt{rescanprefixlength} is determined. This is the length of the 
  the current \texttt{querysuffix} that definitely match some suffix 
  of the subject-sequence. Then the suffix tree is scanned starting at
  \texttt{ploc} to find \texttt{maxloc}. During this matching phase,
  all branching nodes visited are stored in \texttt{matchpath}.
  If \texttt{ploc} is a leaf location, the the corresponding leaf
  is directly processed by the function \texttt{processleaf}.
  Otherwise, the \texttt{nextnode} component of \texttt{ploc}
  is pushed on a stack and a depth first traveral of the 
  the suffix tree below node \texttt{nextnode} is performed.
*/

static Sint enumeratemaxmatches (Maxmatchinfo *maxmatchinfo,
                                 Location *ploc)
{
  Uint rescanprefixlength;

  maxmatchinfo->matchpath.nextfreePathinfo = 0;
  if(maxmatchinfo->depthofpreviousmaxloc > UintConst(1))
  {
    rescanprefixlength = maxmatchinfo->depthofpreviousmaxloc - 1;
  } else
  {
    rescanprefixlength = 0;
  }
  (void) findprefixpathstree (maxmatchinfo->stree, 
                              &maxmatchinfo->matchpath,
                              &maxmatchinfo->maxloc, 
                              ploc,
                              maxmatchinfo->querysuffix
                                  + maxmatchinfo->minmatchlength,
                              maxmatchinfo->query 
			          + maxmatchinfo->querylen - 1,
                              rescanprefixlength);
  maxmatchinfo->depthofpreviousmaxloc 
    = maxmatchinfo->maxloc.locstring.length;
  maxmatchinfo->commondepthstack.nextfreeNodeinfo = 0;
  if(ploc->nextnode.toleaf)
  {
    if(processleaf(LEAFADDR2NUM(maxmatchinfo->stree,ploc->nextnode.address),
                   NULL,(void *) maxmatchinfo) != 0)
    {
      return -1;
    }
  } else
  {
    (void) processbranch1(ploc->nextnode.address,(void *) maxmatchinfo);
    if(depthfirststree(maxmatchinfo->stree,
                       &ploc->nextnode,
                       processleaf,
                       processbranch1,
                       processbranch2,
                       NULL,
                       NULL,
                       (void *) maxmatchinfo) != 0)
    {
      return -2;
    }
  }
  return 0;
}

/*EE
  The following function finds all maximal matches between the 
  subject sequence and the query sequence of length at least
  \texttt{minmatchlength}. To each match the function \texttt{processmatch}
  is applied, with \texttt{processinfo} as its first argument.
  \texttt{query} is the reference to the query, \texttt{querylen} is the
  length of the query and \texttt{queryseqnum} is the number of the
  query sequence. Initially, the function appropriately intializes the
  \texttt{maxmatchinfo}-record. It then scans \texttt{query} to find
  \texttt{ploc} for the longest suffix of \texttt{query}.
  The depth of \texttt{ploc} is stored in \texttt{depthofpreviousmaxloc}.
  In the \texttt{for}-loop each instance of \texttt{ploc} is determined
  and processed further by \texttt{enumeratemaxmatches} whenever its 
  depth is longer than the minimum match length.
*/

Sint findmaxmatches(Suffixtree *stree,
                    vector<Uint*> table,
                    Uint minmatchlength,
                    Processmatchfunction processmatch,
                    void *processinfo,
                    Uchar *query,
                    Uint querylen,
                    Uint queryseqnum)
{
  Uchar *querysubstringend;  // ref to end of querysubs. of len. minmatchl.
  Location ploc;
  Maxmatchinfo maxmatchinfo;
  DEBUG1(2,"query of length %lu=",(Showuint) querylen);
  DEBUGCODE(2,(void) fwrite(query,sizeof(Uchar),(size_t) querylen,stdout));
  DEBUG0(2,"\n");
  DEBUG1(2,"search for matches of minimum length %lu\n",
           (Showuint) minmatchlength);
  if(querylen < minmatchlength)
  {
    return 0;
  }
  maxmatchinfo.stree = stree;
  INITARRAY(&maxmatchinfo.commondepthstack,Nodeinfo);
  INITARRAY(&maxmatchinfo.matchpath,Pathinfo);
  maxmatchinfo.querysuffix = maxmatchinfo.query = query;
  maxmatchinfo.querylen = querylen;
  maxmatchinfo.minmatchlength = minmatchlength;
  maxmatchinfo.queryseqnum = queryseqnum;
  maxmatchinfo.processmatch = processmatch;
  maxmatchinfo.processinfo = processinfo;
  querysubstringend = query + minmatchlength - 1;
  (void) scanprefixfromnodestree (stree, &ploc, ROOT (stree), 
                                  query, querysubstringend,0);
  maxmatchinfo.depthofpreviousmaxloc = ploc.locstring.length;
  for (/* Nothing */;
       querysubstringend < query + querylen - 1; 
       maxmatchinfo.querysuffix++, querysubstringend++)
  {
    //DEBUGCODE(2,showlocation(stdout,stree,&ploc));
    DEBUG0(2,"\n");
    if(ploc.locstring.length >= minmatchlength &&
       enumeratemaxmatches(&maxmatchinfo,&ploc) != 0)
    {
      return -1;
    }
    if (ROOTLOCATION (&ploc))
    {
      (void) scanprefixfromnodestree (stree, &ploc, ROOT (stree), 
                                      maxmatchinfo.querysuffix+1, 
                                      querysubstringend+1,0);
    }
    else
    {
      linklocstree (stree, &ploc, &ploc);
      (void) scanprefixstree (stree, &ploc, &ploc,
                              maxmatchinfo.querysuffix
                                 + ploc.locstring.length+1,
                              querysubstringend+1,0);
    }
  }
  //DEBUGCODE(2,showlocation(stdout,stree,&ploc));
  DEBUG0(2,"\n");
  while (!ROOTLOCATION (&ploc) && ploc.locstring.length >= minmatchlength)
  {
    if(enumeratemaxmatches (&maxmatchinfo,&ploc) != 0)
    {
      return -2;
    }
    linklocstree (stree, &ploc, &ploc);
    maxmatchinfo.querysuffix++;
    //DEBUGCODE(2,showlocation(stdout,stree,&ploc));
    DEBUG0(2,"\n");
  }
  FREEARRAY(&maxmatchinfo.commondepthstack,Nodeinfo);
  FREEARRAY(&maxmatchinfo.matchpath,Pathinfo);
  return 0;
}
