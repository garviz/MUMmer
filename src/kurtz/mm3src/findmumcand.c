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
#include <iostream>
#include <vector>
#include "streedef.h"
#include "debugdef.h"
#include "spacedef.h"
#include "maxmatdef.h"
#include "streeacc.h"
#include "streehuge.h"
#include "protodef.h"
//}
using namespace std;
/*EE
  This module contains functions to compute MUM-candidates using
  a linear time suffix tree traversal. 
*/

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

Uint getlargelinkstree(/*@unused@*/ Suffixtree *stree,Bref btptr,Uint depth)
{
  if(depth == UintConst(1))
  {
    return 0;
  }
  return *(btptr+4);
}

void rescanstree(Suffixtree *stree,Location *loc,
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

void getbranchinfostree(Suffixtree *stree,Uint whichinfo,
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

/*@null@*/ SYMBOL *scanprefixfromnodestree(Suffixtree *stree,Location *loc,
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

void linklocstree(Suffixtree *stree,Location *outloc,Location *inloc)
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

/*@null@*/ SYMBOL *scanprefixstree(Suffixtree *stree,Location *outloc,
                                   Location *inloc,SYMBOL *left,
                                   SYMBOL *right,Uint rescanlength)
{
  Uint prefixlen, remainingtoskip;

  /*DEBUG0(4,"scanprefixstree starts at location ");
  DEBUGCODE(4,showlocation(stdout,stree,inloc));
  DEBUG0(4,"\n");*/
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

/*
  The following function checks if a location \texttt{loc} (of length 
  larger than \texttt{minmatchlength}) in the suffix tree represents 
  a MUM-candiate. The parameters are as follows:

  \begin{enumerate}
  \item
  \texttt{subjectseq} points to the subject sequence
  \item
  \texttt{querysuffix} points to the current suffix of the query sequence
  \item
  \texttt{query} points to the query sequence
  \item
  \texttt{seqnum} is the number of the query sequence currently considered
  \item
  \texttt{processmumcandidate} is the function to further process a 
  MUM-candidate.
  \item
  \texttt{processinfo} points to some values additionally required by
  the function \texttt{processmumcandidate}.
  \end{enumerate}
  By construction, the location in the suffix tree represents a 
  substring of the subject sequence which maximaly matches a prefix of
  \texttt{querysuffix}. Thus it is only necessary to verify that,
  the substring of the subject sequence is long enough, that it
  is unique in the subject sequence and that the match
  is also left maximal. This is done as follows:
  
  \begin{enumerate}
  \item
  does \texttt{loc} represent a substring of length at least 
  \texttt{minmatchlength}?
  \item
  does \texttt{loc} correspond to a leaf edge? Then then the string 
  represented by the location is unique in the subject sequence.
  \item
  is the substring left maximal? This is true if one of the following
  conditions hold:
  \begin{itemize}
  \item
  the suffix of the query currently considered is the first suffix, or 
  \item
  the string represented by \texttt{loc} is a prefix of the subject string,
  or
  \item
  the characters immediately to the left of the matching strings
  in the subject sequence and the query sequence are different
  \end{itemize}
  \end{enumerate}
  If all conditions 1-3 are true, then a function 
  \texttt{processmumcandidate} is called. It takes the necessary 
  information about the MUM-candidate as its arguments.
  In case an error occurs, a negative number is returned. Otherwise,
  0 is returned.
*/

static Sint checkiflocationisMUMcand (Location *loc,
                                      Uchar *subjectseq,
				      Uchar *querysuffix,
				      Uchar *query,
                                      Uint seqnum,
                                      Processmatchfunction 
                                        processmumcandidate,
                                      void *processinfo)
{
  if (loc->remain > 0 
      && loc->nextnode.toleaf
      && (querysuffix == query || loc->locstring.start == 0
			       || *(querysuffix - 1) != 
                                  subjectseq[loc->locstring.start - 1]))
  {
    if(processmumcandidate(processinfo,
                           loc->locstring.length,   // matchlength
	                   loc->locstring.start,    // subject start
                           seqnum,                  // queryseq
                           (Uint) (querysuffix -   
                                   query)) != 0)    // querystart
    {
      return -1;
    }
  }
  return 0;
}

/*EE
  The following function traverses the suffix tree guided by
  some query string. The parameters are as follows:
  \begin{enumerate}
  \item
  \texttt{stree} is the suffix tree constructed from the subject
  sequence.
  \item
  \texttt{minmatchlength} is the minimal length of the MUMs as specified
  \item
  \texttt{processmumcandidate} is the function to further process a 
  MUM-candidate.
  \item
  \texttt{processinfo} points to some values additionally required by
  the function \texttt{processmumcandidate}.
  \item
  \texttt{query} points to the query which is of length 
  \texttt{querylen}
  \item
  \texttt{seqnum} is the number of the current query sequence
  in the \texttt{Multiseq}-record.
  \end{enumerate}
  For each suffix, say \(s\), of the query sequence
  the following function computes the location of the longest prefix of s 
  that is a substring of the subject sequence. This is done
  by iteratively calling the function \texttt{scanprefixfromnodestree}.
  In each step, the scan starts at a location which represents a prefix
  of the maximaly matching substring. The locations are computed
  using the function \texttt{linklocstree}.
  In case an error occurs, a negative number is returned. Otherwise,
  0 is returned.
*/

Sint findmumcandidates(Suffixtree *stree,
                       vector<Uint*> table,
                       Uint minmatchlength,
                       Processmatchfunction processmumcandidate,
                       void *processinfo,
                       Uchar *query,
                       Uint querylen,
                       Uint seqnum)
{
  Uchar *lptr, 
        *right = query + querylen - 1, 
        *querysuffix;
  Location loc;

  DEBUG1(2,"query of length %lu=",(Showuint) querylen);
  DEBUGCODE(2,(void) fwrite(query,sizeof(Uchar),(size_t) querylen,stdout));
  DEBUG0(2,"\n");
  lptr = scanprefixfromnodestree (stree, &loc, ROOT (stree), query, right, 0);
  for (querysuffix = query; lptr != NULL; querysuffix++)
  {
    //DEBUGCODE(2,showlocation(stdout,stree,&loc));
    if(loc.locstring.length >= minmatchlength &&
       checkiflocationisMUMcand(&loc,stree->text, 
                                querysuffix, 
                                query,
                                seqnum,
                                processmumcandidate,
                                processinfo) != 0)
    {
      return -1;
    }
    if (ROOTLOCATION (&loc))
    {
      lptr = scanprefixfromnodestree (stree, &loc, ROOT (stree), 
                                      lptr + 1, right, 0);
    }
    else
    {
      linklocstree (stree, &loc, &loc);
      lptr = scanprefixstree (stree, &loc, &loc, lptr, right, 0);
    }
  }
  //DEBUGCODE(2,showlocation(stdout,stree,&loc));
  while (!ROOTLOCATION (&loc) && loc.locstring.length >= minmatchlength)
  {
    if(checkiflocationisMUMcand (&loc,
                                 stree->text, 
                                 querysuffix, 
                                 query,
                                 seqnum,
                                 processmumcandidate,
                                 processinfo) != 0)
    {
      return -2;
    }
    linklocstree (stree, &loc, &loc);
    querysuffix++;
    //DEBUGCODE(2,showlocation(stdout,stree,&loc));
  }
  return 0;
}
