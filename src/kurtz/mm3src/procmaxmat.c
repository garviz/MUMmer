/*
  Copyright (c) 2003 by Stefan Kurtz and The Institute for
  Genomic Research.  This is OSI Certified Open Source Software.
  Please see the file LICENSE for licensing information and
  the file ACKNOWLEDGEMENTS for names of contributors to the
  code base.
*/

//\IgnoreLatex{

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <google/sparsetable>
#include <vector>
#include <string>
#include <bitset>
#include <iostream>
#include <mpi.h>
#include <math.h>
#include <cstring>
#include "types.h"
#include "debugdef.h"
#include "errordef.h"
#include "protodef.h"
#include "spacedef.h"
#include "streedef.h"
#include "maxmatdef.h"
#include "streehuge.h"
#include "streeacc.h"
#include "visible.h"

using google::sparsetable;
using namespace std;
//}

/*EE
  This file contains functions to appropriately
  call the function \texttt{findmumcandidates} and \texttt{findmaxmatches}
  and to process their result according to the options given by the user.
*/

/*EE
  The following structure contains all information
  required while computing and processing the matches.
*/

typedef struct
{
  Suffixtree stree;            // the suffix tree of the subject-sequence
  vector<Uint*> table;         // Direct acces table
  Multiseq *subjectmultiseq,   // reference to multiseq of subject
           querymultiseq;      // the Multiseq record of the queries
  ArrayMUMcandidate mumcandtab;// a table containing MUM-candidates
                               // when option \texttt{-mum} is on
  Uint minmatchlength,         // minimum length of a match
       maxdesclength,          // maximum length of a description
       currentquerylen;        // length of the current query sequence
  BOOL showstring,             // is option \texttt{-s} on?
       showsequencelengths,    // is option \texttt{-L} on?
       showreversepositions,   // is option \texttt{-c} on?
       forward,                // compute forward matches
       fourcolumn,             // is option \texttt{-F} on?
       reversecomplement,      // compute reverse complement matches
       cmumcand,               // compute MUM candidates
       cmum,                   // compute MUMs
       currentisrcmatch;       // true iff currently rc-matches are computed
} Matchprocessinfo;            // \Typedef{Matchprocessinfo}

//\IgnoreLatex{
#ifndef STARTFACTOR
#define STARTFACTOR 0.5
#endif

#define ADDFACTOR   0.05
#define MINEXTRA    16

#define VALIDINIT     0

#define FUNCLEVEL 4

#define CHECKTEXTLEN\
        if(textlen > MAXTEXTLEN)\
        {\
          ERROR2("suffix tree construction failed: "\
                 "textlen=%lu larger than maximal textlen=%lu",\
                  (Showuint) textlen,(Showuint) MAXTEXTLEN);\
          return -1;\
        }

#define LEASTSHOWPROGRESS 100000
#define NUMOFCALLS 100

#define DECLAREEXTRA\
        Uint j = 0, step, nextstep;\
        stree->nonmaximal = NULL;\
        step = textlen/NUMOFCALLS;\
        nextstep = (textlen >= LEASTSHOWPROGRESS) ? step : (textlen+1);\
        if(progress == NULL && textlen >= LEASTSHOWPROGRESS)\
        {\
          fprintf(stderr,"# process %lu characters per dot\n",\
                 (Showuint) textlen/NUMOFCALLS);\
        }

#define COMPLETELARGEFIRST  completelarge(stree)
#define COMPLETELARGESECOND completelarge(stree)
#define PROCESSHEAD          /* Nothing */

#define CHECKSTEP            if(j == nextstep)\
                             {\
                               if(progress == NULL)\
                               {\
                                 if(nextstep == step)\
                                 {\
                                   fputc('#',stderr);\
                                 }\
                                 fputc('.',stderr);\
                                 fflush(stdout);\
                               } else\
                               {\
                                 progress(nextstep,info);\
                               }\
                               nextstep += step;\
                             }\
                             j++

#define FINALPROGRESS        if(textlen >= LEASTSHOWPROGRESS)\
                             {\
                               if(finalprogress == NULL)\
                               {\
                                 fputc('\n',stderr);\
                               } else\
                               {\
                                 finalprogress(info);\
                               }\
                             }

/*
  The function \emph{taillcp} computes the length of the longest common prefix
  of two strings. The first string is between pointers \emph{start1} and 
  \emph{end1}. The second string is the current tail, which is between  the
  pointers \emph{tailptr} and \emph{sentinel}.
*/

static Uint taillcp(Suffixtree *stree,SYMBOL *start1, SYMBOL *end1)
{
  SYMBOL *ptr1 = start1, *ptr2 = stree->tailptr + 1;
  while(ptr1 <= end1 && ptr2 < stree->sentinel && *ptr1 == *ptr2)
  {
    ptr1++;
    ptr2++;
  }
  return (Uint) (ptr1-start1);
}

/*
 The function \emph{scanprefix} scans a prefix of the current tail 
 down from a given node.
*/

static void scanprefix(Suffixtree *stree)
{
  Uint *nodeptr = NULL, *largeptr = NULL, leafindex, nodedepth, edgelen, node, 
       distance = 0, prevnode, prefixlen, headposition;
  SYMBOL *leftborder = (SYMBOL *) NULL, tailchar, edgechar = 0;

  if(stree->headnodedepth == 0)   // headnode is root
  {
    if(stree->tailptr == stree->sentinel)   // there is no \$-edge
    {
      stree->headend = NULL;
      return;
    }
    tailchar = *(stree->tailptr);
    if((node = stree->rootchildren[(Uint) tailchar]) == UNDEFINEDREFERENCE)
    {
      stree->headend = NULL;   
      return;
    }
    if(ISLEAF(node)) // successor edge is leaf, compare tail and leaf edge label
    {
      leftborder = stree->text + GETLEAFINDEX(node);
      prefixlen = 1 + taillcp(stree,leftborder+1,stree->sentinel-1);
      (stree->tailptr) += prefixlen;
      stree->headstart = leftborder;
      stree->headend = leftborder + (prefixlen-1);
      stree->insertnode = node;
      return;
    }
    nodeptr = stree->branchtab + GETBRANCHINDEX(node);
    GETBOTH(nodedepth,headposition,nodeptr);  // get info for branch node
    leftborder = stree->text + headposition;
    prefixlen = 1 + taillcp(stree,leftborder+1,leftborder + nodedepth - 1);
    (stree->tailptr)+= prefixlen;
    if(nodedepth > prefixlen)   // cannot reach the successor, fall out of tree
    {
      stree->headstart = leftborder;
      stree->headend = leftborder + (prefixlen-1);
      stree->insertnode = node;
      return;
    }
    stree->headnode = nodeptr;
    stree->headnodedepth = nodedepth;
  }
  while(True)  // \emph{headnode} is not the root
  {
    prevnode = UNDEFINEDREFERENCE;
    node = GETCHILD(stree->headnode);
    if(stree->tailptr == stree->sentinel)  //  \$-edge
    {
      do // there is no \$-edge, so find last successor, of which it becomes right brother
      {
        prevnode = node; 
        if(ISLEAF(node))
        {
          node = LEAFBROTHERVAL(stree->leaftab[GETLEAFINDEX(node)]);
        } else
        {
          node = GETBROTHER(stree->branchtab + GETBRANCHINDEX(node));
        }
      } while(!NILPTR(node));
      stree->insertnode = NILBIT;
      stree->insertprev = prevnode;
      stree->headend = NULL;
      return;
    } 
    tailchar = *(stree->tailptr);

    do // find successor edge with firstchar = tailchar
    {
      if(ISLEAF(node))   // successor is leaf
      {
        leafindex = GETLEAFINDEX(node);
        leftborder = stree->text + (stree->headnodedepth + leafindex);
        if((edgechar = *leftborder) >= tailchar)   // edge will not come later
        {
          break;
        }
        prevnode = node;
        node = LEAFBROTHERVAL(stree->leaftab[leafindex]);
      } else  // successor is branch node
      {
        nodeptr = stree->branchtab + GETBRANCHINDEX(node);
        GETONLYHEADPOS(headposition,nodeptr);
        leftborder = stree->text + (stree->headnodedepth + headposition);
        if((edgechar = *leftborder) >= tailchar)  // edge will not come later
        {
          break;
        }
        prevnode = node;
        node = GETBROTHER(nodeptr);
      }
    } while(!NILPTR(node));
    if(NILPTR(node) || edgechar > tailchar)  // edge not found
    {
      stree->insertprev = prevnode;   // new edge will become brother of this
      stree->headend = NULL;
      return;
    } 
    if(ISLEAF(node))  // correct edge is leaf edge, compare its label with tail
    {
      prefixlen = 1 + taillcp(stree,leftborder+1,stree->sentinel-1);
      (stree->tailptr) += prefixlen;
      stree->headstart = leftborder;
      stree->headend = leftborder + (prefixlen-1);
      stree->insertnode = node;
      stree->insertprev = prevnode;
      return;
    }
    GETDEPTHAFTERHEADPOS(nodedepth,nodeptr); // we already know headposition
    edgelen = nodedepth - stree->headnodedepth;
    prefixlen = 1 + taillcp(stree,leftborder+1,leftborder + edgelen - 1);
    (stree->tailptr) += prefixlen;
    if(edgelen > prefixlen)  // cannot reach next node
    {
      stree->headstart = leftborder;
      stree->headend = leftborder + (prefixlen-1);
      stree->insertnode = node;
      stree->insertprev = prevnode;
      return;
    } 
    stree->headnode = nodeptr;
    stree->headnodedepth = nodedepth;
  }
}

/*
  The function \emph{insertleaf} inserts a leaf and a corresponding leaf
  edge outgoing from the current \emph{headnode}. 
  \emph{insertprev} refers to the node to the left of the leaf to be inserted.
  If the leaf is the first child, then \emph{insertprev} is 
  \texttt{UNDEFINEDREFERENCE}.
*/

static void insertleaf(Suffixtree *stree)
{
  Uint *ptr, newleaf;

  newleaf = MAKELEAF(stree->nextfreeleafnum);
  DEBUGCODE(1,stree->insertleafcalls++);
  if(stree->headnodedepth == 0)                // head is the root
  {
    if(stree->tailptr != stree->sentinel)      // no \$-edge initially
    {
      stree->rootchildren[(Uint) *(stree->tailptr)] = newleaf;
      *(stree->nextfreeleafptr) = VALIDINIT;
      DEBUG2(4,"%c-edge from root points to leaf %lu\n",
               *(stree->tailptr),(Showuint) stree->nextfreeleafnum);
    }
  } else
  {
    if (stree->insertprev == UNDEFINEDREFERENCE)  // newleaf = first child
    {
      *(stree->nextfreeleafptr) = GETCHILD(stree->headnode);
      SETCHILD(stree->headnode,newleaf);
    } else
    {
      if(ISLEAF(stree->insertprev))   // previous node is leaf
      {
        ptr = stree->leaftab + GETLEAFINDEX(stree->insertprev);
        *(stree->nextfreeleafptr) = LEAFBROTHERVAL(*ptr);
        SETLEAFBROTHER(ptr,newleaf);
      } else   // previous node is branching node
      {
        ptr = stree->branchtab + GETBRANCHINDEX(stree->insertprev);
        *(stree->nextfreeleafptr) = GETBROTHER(ptr);
        SETBROTHER(ptr,newleaf);
      }
    }
  }
  RECALLSUCC(newleaf);     // recall node on successor path of \emph{headnode}
  stree->nextfreeleafnum++;
  stree->nextfreeleafptr++;
}

/*
 Before a new node is stored, we check if there is enough space available.
 If not, the space is enlarged by a small amount. Since some global pointers
 directly refer into the table, these have to be adjusted after reallocation.
*/

static void spaceforbranchtab(Suffixtree *stree)
{
  DEBUG1(FUNCLEVEL,">%s\n",__func__);

  if(stree->nextfreebranch >= stree->firstnotallocated)
  {
    Uint tmpheadnode, 
         tmpchainstart = 0, 
         extra = (Uint) (ADDFACTOR * (MULTBYSMALLINTS(stree->textlen+1)));
    if(extra < MINEXTRA)
    {
      extra = MULTBYSMALLINTS(MINEXTRA);
    }
    DEBUG1(2,"#all suffixes up to suffix %lu have been scanned\n",
              (Showuint) stree->nextfreeleafnum);
    DEBUG1(2,"#to get %lu extra space do ",(Showuint) extra);
    stree->currentbranchtabsize += extra;
    tmpheadnode = BRADDR2NUM(stree,stree->headnode);
    if(stree->chainstart != NULL)
    {
      tmpchainstart = BRADDR2NUM(stree,stree->chainstart);
    }

    stree->branchtab 
     = ALLOCSPACE(stree->branchtab,Uint,stree->currentbranchtabsize);
    stree->nextfreebranch = stree->branchtab + stree->nextfreebranchnum;
    stree->headnode = stree->branchtab + tmpheadnode;
    if(stree->chainstart != NULL)
    {
      stree->chainstart = stree->branchtab + tmpchainstart;
    }
    stree->firstnotallocated 
       = stree->branchtab + stree->currentbranchtabsize - LARGEINTS;
  }
}

/*
  The function \emph{insertbranch} inserts a branching node and splits
  the appropriate edges, according to the canonical location of the current
  head. \emph{insertprev} refers to the node to the left of the branching
  node to be inserted. If the branching node is the first child, then 
  \emph{insertprev} is \texttt{UNDEFINEDREFERENCE}. The edge to be split ends
  in the node referred to by \emph{insertnode}.
*/

static void insertbranchnode(Suffixtree *stree)
{
  Uint *ptr, *insertnodeptr, *insertleafptr, insertnodeptrbrother; 

  spaceforbranchtab(stree);
  if(stree->headnodedepth == 0)      // head is the root
  {
    stree->rootchildren[(Uint) *(stree->headstart)] 
      = MAKEBRANCHADDR(stree->nextfreebranchnum);
    *(stree->nextfreebranch+1) = VALIDINIT;
    DEBUG2(4,"%c-edge from root points to branch node with address %lu\n",
           *(stree->headstart),(Showuint) stree->nextfreebranchnum);
  } else
  {
    if(stree->insertprev == UNDEFINEDREFERENCE)  // new branch = first child
    {
      SETCHILD(stree->headnode,MAKEBRANCHADDR(stree->nextfreebranchnum));
    } else
    {
      if(ISLEAF(stree->insertprev))  // new branch = right brother of leaf
      {
        ptr = stree->leaftab + GETLEAFINDEX(stree->insertprev);
        SETLEAFBROTHER(ptr,MAKEBRANCHADDR(stree->nextfreebranchnum));
      } else                     // new branch = brother of branching node
      {
        SETBROTHER(stree->branchtab + GETBRANCHINDEX(stree->insertprev),
                   MAKEBRANCHADDR(stree->nextfreebranchnum));
      }
    }
  }
  if(ISLEAF(stree->insertnode))   // split edge is leaf edge
  {
    DEBUGCODE(1,stree->splitleafedge++);
    insertleafptr = stree->leaftab + GETLEAFINDEX(stree->insertnode);
    if (stree->tailptr == stree->sentinel || 
        *(stree->headend+1) < *(stree->tailptr)) 
    {
      SETNEWCHILDBROTHER(MAKELARGE(stree->insertnode),  // first child=oldleaf
                         LEAFBROTHERVAL(*insertleafptr));  // inherit brother
      RECALLNEWLEAFADDRESS(stree->nextfreeleafptr);
      SETLEAFBROTHER(insertleafptr,                     // new leaf =
                     MAKELEAF(stree->nextfreeleafnum)); // right brother of old leaf
    } else
    {
      SETNEWCHILDBROTHER(MAKELARGELEAF(stree->nextfreeleafnum),  // first child=new leaf
                         LEAFBROTHERVAL(*insertleafptr));  // inherit brother
      *(stree->nextfreeleafptr) = stree->insertnode;  // old leaf = right brother of of new leaf
      RECALLLEAFADDRESS(insertleafptr);
    }
  } else  // split edge leads to branching node
  {
    DEBUGCODE(1,stree->splitinternaledge++);
    insertnodeptr = stree->branchtab + GETBRANCHINDEX(stree->insertnode);
    insertnodeptrbrother = GETBROTHER(insertnodeptr);
    if (stree->tailptr == stree->sentinel || 
        *(stree->headend+1) < *(stree->tailptr)) 
    {
      SETNEWCHILDBROTHER(MAKELARGE(stree->insertnode), // first child new branch
                         insertnodeptrbrother);        // inherit right brother
      RECALLNEWLEAFADDRESS(stree->nextfreeleafptr);
      SETBROTHER(insertnodeptr,MAKELEAF(stree->nextfreeleafnum)); // new leaf = brother of old branch
    } else
    {
      SETNEWCHILDBROTHER(MAKELARGELEAF(stree->nextfreeleafnum), // first child is new leaf
                         insertnodeptrbrother);        // inherit brother
      *(stree->nextfreeleafptr) = stree->insertnode;   // new branch is brother of new leaf
      RECALLBRANCHADDRESS(insertnodeptr);
    }
  }
  SETNILBIT;
  RECALLSUCC(MAKEBRANCHADDR(stree->nextfreebranchnum)); // node on succ. path
  stree->currentdepth = stree->headnodedepth + (Uint) (stree->headend-stree->headstart+1);
  SETDEPTHHEADPOS(stree->currentdepth,stree->nextfreeleafnum);
  SETMAXBRANCHDEPTH(stree->currentdepth);
  stree->nextfreeleafnum++;
  stree->nextfreeleafptr++;
  DEBUGCODE(1,stree->nodecount++);
}

static void initSuffixtree(Suffixtree *stree,SYMBOL *text,Uint textlen)
{
  Uint i, *ptr;

  DEBUG1(4,">%s\n",__func__);
  DEBUG1(2,"# MULTBYSMALLINTS(textlen+1)=%lu\n",
           (Showuint) MULTBYSMALLINTS(textlen+1));
  DEBUG1(2,"# STARTFACTOR=%.2f\n",STARTFACTOR);
  DEBUG1(2,"# MINEXTRA=%lu\n",(Showuint) MINEXTRA);
  stree->currentbranchtabsize 
    = (Uint) (STARTFACTOR * MULTBYSMALLINTS(textlen+1));
  if(stree->currentbranchtabsize < MINEXTRA)
  {
    stree->currentbranchtabsize = MULTBYSMALLINTS(MINEXTRA);
  }
  stree->leaftab = ALLOCSPACE(NULL,Uint,textlen+2);
  stree->rootchildren = ALLOCSPACE(NULL,Uint,LARGESTCHARINDEX + 1);
  stree->branchtab = ALLOCSPACE(NULL,Uint,stree->currentbranchtabsize);

  stree->text = stree->tailptr = text;
  stree->textlen = textlen;
  stree->sentinel = text + textlen;
  stree->firstnotallocated 
    = stree->branchtab + stree->currentbranchtabsize - LARGEINTS;
  stree->headnode = stree->nextfreebranch = stree->branchtab;
  stree->headend = NULL;
  stree->headnodedepth = stree->maxbranchdepth = 0;
  for(ptr=stree->rootchildren; ptr<=stree->rootchildren+LARGESTCHARINDEX; ptr++)
  {
    *ptr = UNDEFINEDREFERENCE;
  }
  for(i=0; i<LARGEINTS; i++)
  {
    stree->branchtab[i] = 0;
  }
  stree->nextfreebranch = stree->branchtab;
  stree->nextfreebranchnum = 0;
  SETDEPTHHEADPOS(0,0);
  SETNEWCHILDBROTHER(MAKELARGELEAF(0),0);
  SETBRANCHNODEOFFSET;
  stree->rootchildren[(Uint) *text] = MAKELEAF(0);
  stree->leaftab[0] = VALIDINIT;
  DEBUG2(4,"%c-edge from root points to leaf %lu\n",*text,(Showuint) 0);
  stree->leafcounts = NULL;
  stree->nextfreeleafnum = 1;
  stree->nextfreeleafptr = stree->leaftab + 1;
  stree->nextfreebranch = stree->branchtab + LARGEINTS;
  stree->nextfreebranchnum = LARGEINTS;
  stree->insertnode = stree->insertprev = UNDEFINEDREFERENCE;
  stree->smallnotcompleted = 0;
  stree->chainstart = NULL;
  stree->largenode = stree->smallnode = 0;

//\Ignore{

#ifdef DEBUG
  stree->showsymbolstree = NULL;
  stree->alphabet = NULL;
  stree->nodecount = 1;
  stree->splitleafedge = 
  stree->splitinternaledge = 
  stree->artificial = 
  stree->multiplications = 0;
  stree->insertleafcalls = 1;
  stree->maxset = stree->branchtab + LARGEINTS - 1;
  stree->largelinks = stree->largelinkwork = stree->largelinklinkwork = 0;
#endif

//}

}

static Uint getlargelinkconstruction(Suffixtree *stree)
{
  SYMBOL secondchar;

  DEBUG2(FUNCLEVEL,">%s(%lu)\n",
                   __func__,
                   (Showuint) BRADDR2NUM(stree,stree->headnode));
  if(stree->headnodedepth == 1)
  {
    return 0;        // link refers to root
  }
  if(stree->headnodedepth == 2)  // determine second char of egde
  {
    if(stree->headend == NULL)
    {
      secondchar = *(stree->tailptr-1);
    } else
    {
      secondchar = *(stree->tailptr - (stree->headend - stree->headstart + 2));
    }
    return stree->rootchildren[(Uint) secondchar]; 
  }
  return *(stree->headnode+4);
}

static void rescan (Suffixtree *stree)
{
  Uint *nodeptr, *largeptr = NULL, distance = 0, node, prevnode, 
       nodedepth, edgelen, wlen, leafindex, headposition;
  SYMBOL headchar, edgechar;

  if(stree->headnodedepth == 0)   // head is the root
  {
    headchar = *(stree->headstart);  // headstart is assumed to be not empty
    node = stree->rootchildren[(Uint) headchar];
    if(ISLEAF(node))   // stop if successor is leaf
    {
      stree->insertnode = node;
      return;
    } 
    nodeptr = stree->branchtab + GETBRANCHINDEX(node);
    GETONLYDEPTH(nodedepth,nodeptr);
    wlen = (Uint) (stree->headend - stree->headstart + 1);
    if(nodedepth > wlen)    // cannot reach the successor node
    {
      stree->insertnode = node;
      return;
    }
    stree->headnode = nodeptr;        // go to successor node
    stree->headnodedepth = nodedepth;
    if(nodedepth == wlen)             // location has been scanned
    {
      stree->headend = NULL;
      return;
    }
    (stree->headstart) += nodedepth;
  }
  while(True)   // \emph{headnode} is not the root
  {
    headchar = *(stree->headstart);  // \emph{headstart} is assumed to be nonempty
    prevnode = UNDEFINEDREFERENCE;
    node = GETCHILD(stree->headnode);
    while(True)             // traverse the list of successors
    {
      if(ISLEAF(node))   // successor is leaf
      {
        leafindex = GETLEAFINDEX(node);
        edgechar = stree->text[stree->headnodedepth + leafindex];
        if(edgechar == headchar)    // correct edge found
        {
          stree->insertnode = node;
          stree->insertprev = prevnode;
          return;
        }
        prevnode = node;
        node = LEAFBROTHERVAL(stree->leaftab[leafindex]);  
      } else   // successor is branch node
      {
        nodeptr = stree->branchtab + GETBRANCHINDEX(node);
        GETONLYHEADPOS(headposition,nodeptr);
        edgechar = stree->text[stree->headnodedepth + headposition];
        if(edgechar == headchar) // correct edge found
        {
          break;
        } 
        prevnode = node;
        node = GETBROTHER(nodeptr);
      }
    }

    GETDEPTHAFTERHEADPOS(nodedepth,nodeptr);     // get info about succ node
    edgelen = nodedepth - stree->headnodedepth;
    wlen = (Uint) (stree->headend - stree->headstart + 1);
    if(edgelen > wlen)     // cannot reach the succ node
    {
      stree->insertnode = node;
      stree->insertprev = prevnode;
      return;
    }
    stree->headnode = nodeptr;    // go to the successor node
    stree->headnodedepth = nodedepth;
    if(edgelen == wlen)                    // location is found
    {
      stree->headend = NULL;
      return;
    }
    (stree->headstart) += edgelen;
  }
}

/*
  The function \emph{completelarge} is called whenever a large node 
  is inserted. It basically sets the appropriate distance values of the small
  nodes of the current chain.
*/

static void completelarge(Suffixtree *stree)
{
  Uint distance, *backwards;

  if(stree->smallnotcompleted > 0)
  {
    backwards = stree->nextfreebranch;
    for(distance = 1; distance <= stree->smallnotcompleted; distance++)
    {
      backwards -= SMALLINTS;
      SETDISTANCE(backwards,distance);
    }
    stree->smallnotcompleted = 0;
    stree->chainstart = NULL;
  }
  stree->nextfreebranch += LARGEINTS;
  stree->nextfreebranchnum += LARGEINTS;
  stree->largenode++;
}

/*
  The function \emph{linkrootchildren} constructs the successor chain
  for the children of the root. This is done at the end of the algorithm
  in one sweep over table \emph{rootchildren}.
*/

static void linkrootchildren(Suffixtree *stree)
{
  Uint *rcptr, *prevnodeptr, prev = UNDEFINEDREFERENCE;

  stree->alphasize = 0;
  for(rcptr = stree->rootchildren; 
      rcptr <= stree->rootchildren + LARGESTCHARINDEX; rcptr++)
  {
    if(*rcptr != UNDEFINEDREFERENCE)
    {
      stree->alphasize++;
      if(prev == UNDEFINEDREFERENCE)
      {
        SETCHILD(stree->branchtab,MAKELARGE(*rcptr));
      } else
      {
        if(ISLEAF(prev))
        {
          stree->leaftab[GETLEAFINDEX(prev)] = *rcptr;
        } else
        {
          prevnodeptr = stree->branchtab + GETBRANCHINDEX(prev);
          SETBROTHER(prevnodeptr,*rcptr);
        }
      }
      prev = *rcptr;
    }
  }
  if(ISLEAF(prev))
  {
    stree->leaftab[GETLEAFINDEX(prev)] = MAKELEAF(stree->textlen);
  } else
  {
    prevnodeptr = stree->branchtab + GETBRANCHINDEX(prev);
    SETBROTHER(prevnodeptr,MAKELEAF(stree->textlen));
  }
  stree->leaftab[stree->textlen] = NILBIT;
}

Sint constructprogressstree(Suffixtree *stree,SYMBOL *text,
                            Uint textlen,
                            void (*progress)(Uint,void *),
                            void (*finalprogress)(void *),
                            void *info)
{
  DECLAREEXTRA;

  CHECKTEXTLEN;

  initSuffixtree(stree,text,textlen);
  while(stree->tailptr < stree->sentinel || 
        stree->headnodedepth != 0 || stree->headend != NULL)
  {
    CHECKSTEP;
    // case (1): headloc is root
    if(stree->headnodedepth == 0 && stree->headend == NULL) 
    {
      (stree->tailptr)++;
      scanprefix(stree);
    } else
    {
      if(stree->headend == NULL)  // case (2.1): headloc is a node
      {
        FOLLOWSUFFIXLINK;
        scanprefix(stree);
      } else               // case (2.2)
      {
        if(stree->headnodedepth == 0) // case (2.2.1): at root: do not use links
        {
          if(stree->headstart == stree->headend)  // rescan not necessary
          {
            stree->headend = NULL;
          } else
          {
            (stree->headstart)++;
            rescan(stree);
          }
        } else
        {
          FOLLOWSUFFIXLINK;    // case (2.2.2)
          rescan(stree);
        }
        if(stree->headend == NULL)  // case (2.2.3): headloc is a node
        {
          SETSUFFIXLINK(BRADDR2NUM(stree,stree->headnode));
          COMPLETELARGEFIRST;
          scanprefix(stree);
        } else
        {
          if(stree->smallnotcompleted == MAXDISTANCE)  // artifical large node
          {
            DEBUGCODE(1,stree->artificial++);
            DEBUG1(3,"#artifical large node %lu\n",
                      (Showuint) stree->nextfreebranchnum);
            SETSUFFIXLINK(stree->nextfreebranchnum + LARGEINTS);
            COMPLETELARGESECOND;
          } else
          { 
            if(stree->chainstart == NULL)
            {
              stree->chainstart = stree->nextfreebranch;   // start new chain
            } 
            (stree->smallnotcompleted)++;
            (stree->nextfreebranch) += SMALLINTS;      // case (2.2.4)
            (stree->nextfreebranchnum) += SMALLINTS;
            stree->smallnode++;
          }
        }
      } 
    }

    PROCESSHEAD;

    if(stree->headend == NULL)
    {
      insertleaf(stree);  // case (a)
    } else
    {
      insertbranchnode(stree);  // case (b)
    }
  }
  stree->chainstart = NULL;
  linkrootchildren(stree);

//\Ignore{

  DEBUG1(2,"#integers for branchnodes %lu\n",
           (Showuint) stree->nextfreebranchnum);
  DEBUG4(2,"#small %lu large %lu textlen %lu all %lu ",
            (Showuint) stree->smallnode,(Showuint) stree->largenode,
            (Showuint) stree->textlen,
            (Showuint) (stree->smallnode+stree->largenode));
  DEBUG1(2,"ratio %f\n",
         (double) (stree->smallnode+stree->largenode)/stree->nextfreeleafnum);
  DEBUG1(2,"#splitleafedge = %lu\n",(Showuint) stree->splitleafedge);
  DEBUG1(2,"#splitinternaledge = %lu\n",(Showuint) stree->splitinternaledge);
  DEBUG1(2,"#insertleafcalls = %lu\n",(Showuint) stree->insertleafcalls);
  DEBUG1(2,"#artificial = %lu\n",(Showuint) stree->artificial);
  DEBUG1(2,"#multiplications = %lu\n",(Showuint) stree->multiplications);

//}
  FINALPROGRESS;
  return 0;
}

void freestree(Suffixtree *stree)
{
  FREESPACE(stree->leaftab);
  FREESPACE(stree->rootchildren);
  FREESPACE(stree->branchtab);
  if(stree->nonmaximal != NULL)
  {
    FREESPACE(stree->nonmaximal);
  }
  if(stree->leafcounts != NULL)
  {
    FREESPACE(stree->leafcounts);
  }
}

static void showthesymbolstring(FILE *fp,SYMBOL *tlast,SYMBOL *left,
                                SYMBOL *right)
{
  SYMBOL *ptr;

  for(ptr=left; ptr<=right; ptr++)
  {
    if(ptr == tlast)
    {
      (void) putc('~',fp);
      return;
     } 
    if(ptr > left + 10)
    {
      fprintf(fp,"...");
      return;
     }
    SHOWCHARFP(fp,*ptr);
   }
}

Uint getEdgelength(Uchar *left,Uchar *right)
{
    return (Uint)(right-left+1);
}

Uint encoding(Uchar *example, Uint wordsize) 
{
    cout << example << endl;
    const int len=3*wordsize;
    string binary;
    for (int i=0, j=len-1; i<wordsize; i++, j-=3) 
    {
        switch (*(example+i))
        {
            case 'A':
                binary.append("100");
                break;
            case 'a': 
                binary.append("100");
                break;
            case 'C':
                binary.append("101");
                break;
            case 'c':
                binary.append("101");
                break;
            case 'G':
                binary.append("110");
                break;
            case 'g':
                binary.append("110");
                break;
            case 'T':
                binary.append("111");
                break;
            case 't':
                binary.append("111");
                break;
            default:
                break;
        }
   } 
   bitset<32> number(binary);
   return (Uint) number.to_ulong();
}

/* 
 * ===  FUNCTION  ======================================================================
 *         Name:  splitsubstreeH
 *  Description:  Traverse every branch of suffix tree and it stops when it
 *  reaches the max characters to save in table.
 * =====================================================================================
 */
static void splitsubstreeH(Suffixtree *stree, vector<Uint*> &table, Uchar *buffer,Uint *btptr, Uint wordsize)
{
  Uint *largeptr, *succptr, leafindex, succdepth, edgelen, succ, distance, 
       depth, headposition;
  SYMBOL *leftpointer;
  int i;
  
  size_t size = strlen((const char*)buffer);
  if (size>wordsize) 
  {
      cout << size << " no ir mas abajo" << endl;
      return;
  } 

  GETBOTH(depth,headposition,btptr);
  succ = GETCHILD(btptr);
  do 
  {
    if(ISLEAF(succ))
    {
      leafindex = GETLEAFINDEX(succ);
      leftpointer = stree->text + depth + leafindex;
      SYMBOL *ptr;
      if ((size+getEdgelength(leftpointer,stree->sentinel))>wordsize)
          table[encoding(buffer,wordsize)]=btptr;
      else
      {
          for (i=0, ptr=leftpointer; ptr<=stree->sentinel; ptr++, i++)
          {
              if (ptr == stree->sentinel) 
              {
                 buffer[size+i]='\0';
                 break;
              }
              buffer[size+i]=*ptr;
          }
          table[encoding(buffer,wordsize)]=(Uint*)succ;
      }
      succ = LEAFBROTHERVAL(stree->leaftab[leafindex]);
     } else
     {
      succptr = stree->branchtab + GETBRANCHINDEX(succ);
      GETBOTH(succdepth,headposition,succptr);
      leftpointer = stree->text + depth + headposition;
      edgelen = succdepth - depth;
      showthesymbolstring(stdout,stree->sentinel,leftpointer,leftpointer + edgelen - 1);
      SYMBOL *ptr, *end;
      end=leftpointer + edgelen - 1;
      if ((size+edgelen)<wordsize)
      {
          for (i=0, ptr=leftpointer; i<edgelen; ptr++, i++)
              buffer[size+i]=*ptr;
          buffer[size+i]='\0';
          splitsubstreeH(stree,table,buffer,succptr,wordsize);
      }
      table[encoding(buffer,wordsize)]=btptr;
      succ = GETBROTHER(succptr);
    }  
   } while(!NILPTR(succ));
} 

static void createTable(Suffixtree *stree, vector<Uint*> &table, Uint wordsize) 
{ 
    Uint *largeptr, *btptr, *succptr, *rcptr, i, succdepth, distance, 
         nodeaddress, succ, depth, child, brother, headposition, suffixlink;
    Uint leafindex, edgelen;
    Uchar *leftpointer, *buffer;
    buffer = (Uchar *)malloc(sizeof(Uchar *)*wordsize);
    for(rcptr = stree->rootchildren; 
        rcptr <= stree->rootchildren + LARGESTCHARINDEX;rcptr++)
    { 
        if(*rcptr != UNDEFINEDREFERENCE)
         {
             if (ISLEAF(*rcptr))
                 continue;
             else
             {
                 buffer[0]=(Uchar) (rcptr - stree->rootchildren);
                 buffer[1]='\0';
                 btptr = stree->branchtab + GETBRANCHINDEX(*rcptr);
                 switch(buffer[0])
                 {
                     case 'a':
                         splitsubstreeH(stree,table,buffer,btptr,wordsize);
                         break;
                     case 'A':
                         splitsubstreeH(stree,table,buffer,btptr,wordsize);
                         break;
                     case 'c':
                         splitsubstreeH(stree,table,buffer,btptr,wordsize);
                         break;
                     case 'C':
                         splitsubstreeH(stree,table,buffer,btptr,wordsize);
                         break;
                     case 'g':
                         splitsubstreeH(stree,table,buffer,btptr,wordsize);
                         break;
                     case 'G':
                         splitsubstreeH(stree,table,buffer,btptr,wordsize);
                         break;
                     case 't':
                         splitsubstreeH(stree,table,buffer,btptr,wordsize);
                         break;
                     case 'T':
                         splitsubstreeH(stree,table,buffer,btptr,wordsize);
                         break;
                     default:
                         break;
                 }
             }
          }
      }
} 

/*
  The following is the type for the functions to finding maximal matches or
  MUM candidates.
*/

typedef Sint (*Findmatchfunction)(Suffixtree *,
                                  vector<Uint*>,
                                  Uint,
                                  Processmatchfunction,
                                  void *,
                                  Uchar *,
                                  Uint,
                                  Uint);

/*
  The following function is imported from \texttt{findmumcand.c}.
*/

Sint findmumcandidates(Suffixtree *stree,
                       vector<Uint*>,
                       Uint minmatchlength,
                       Processmatchfunction processmatch,
                       void *processinfo,
                       Uchar *query,
                       Uint querylen,
                       Uint seqnum);

/*
  The following function is imported from \texttt{findmaxmat.c}
*/

Sint findmaxmatches(Suffixtree *stree,
                    vector<Uint*>,
                    Uint minmatchlength,
                    Processmatchfunction processmatch,
                    void *processinfo,
                    Uchar *query,
                    Uint querylen,
                    Uint seqnum);

/*
  The following function is imported from \texttt{maxmatinp.c}
*/

Sint scanmultiplefastafile (Multiseq *multiseq,
                            char *filename,
                            Uchar replacewildcardchar,
                            Uchar *input,
                            Uint inputlen);

//}

/*EE
  The following code fragement is used when computing MUMs.
  It calls the function \texttt{mumuniqueinquery}.
  The MUM-candidates are stored in the dynamic 
  array \texttt{mumcandtab}.  After the real MUMs are output, the table 
  of MUM-candidates are declared to be empty.
*/

#define PROCESSREALMUMS\
        if(matchprocessinfo->cmum)\
        {\
          if(mumuniqueinquery(info,\
                              matchprocessinfo->showstring ?\
                                 showseqandmaximalmatch :\
                                 showmaximalmatch,\
                              &matchprocessinfo->mumcandtab) != 0)\
          {\
            return -2;\
          }\
          matchprocessinfo->mumcandtab.nextfreeMUMcandidate = 0;\
        }

/*
  The following function assigns for a given base the corresponding
  complement character. It also handles wild card characters 
  appropriately.
*/

#define ASSIGNMAXMATCOMPLEMENT(VL,VR)\
        if((VR) >= MMREPLACEMENTCHARQUERY)\
        {\
          VL = VR;\
        } else\
        {\
          switch (VR)\
          {\
            case 'a':\
              VL = (Uchar) 't';\
              break;\
            case 'c':\
              VL = (Uchar) 'g';\
              break;\
            case 'g':\
              VL = (Uchar) 'c';\
              break;\
            case 't':\
              VL = (Uchar) 'a';\
              break;\
            case 'r':                       /* a or g */\
              VL = (Uchar) 'y';\
              break;\
            case 'y':                       /* c or t */\
              VL = (Uchar) 'r';\
              break;\
            case 's':                       /* c or g */\
              VL = (Uchar) 's';\
              break;\
            case 'w':                       /* a or t */\
              VL = (Uchar) 'w';\
              break;\
            case 'm':                       /* a or c */\
              VL = (Uchar) 'k';\
              break;\
            case 'k':                       /* g or t */\
              VL = (Uchar) 'm';\
              break;\
            case 'b':                       /* c, g or t */\
              VL = (Uchar) 'v';\
              break;\
            case 'd':                       /* a, g or t */\
              VL = (Uchar) 'h';\
              break;\
            case 'h':                       /* a, c or t */\
              VL = (Uchar) 'd';\
              break;\
            case 'v':                       /* a, c or g */\
              VL = (Uchar) 'b';\
              break;\
            default:                        /* anything */\
              VL = (Uchar) 'n';\
              break;\
          }\
        }

/*
  The following function computes the Watson-Crick complement
  of the sequence pointed to by \texttt{seq}. The sequnce is
  of length \texttt{seqlen}. The result is computed in-place.
*/

static void wccSequence (Uchar *seq,
                         Uint seqlen)
{
  Uchar *front, *back, tmp = 0;

  for (front = seq, back = seq + seqlen - 1; 
       front <= back; front++, back--)
  {
    ASSIGNMAXMATCOMPLEMENT (tmp, *front);
    ASSIGNMAXMATCOMPLEMENT (*front, *back);
    *back = tmp;
  }
}

/*
  The following function shows the sequence description of sequence
  number \texttt{seqnum} in \texttt{multiseq}.
*/

static void showsequencedescription(Multiseq *multiseq, Uint maxdesclength,
                                    Uint seqnum)
{
  Uint i, desclength = DESCRIPTIONLENGTH(multiseq,seqnum);
  Uchar *desc = DESCRIPTIONPTR(multiseq,seqnum);

  for(i=0; i<desclength; i++)
  {
    if(isspace((Ctypeargumenttype) desc[i]))
    {
      break;
    }
    (void) putchar((Fputcfirstargtype) desc[i]);
  }
  if(desclength < maxdesclength)
  {
    for(i=0; i < maxdesclength - desclength; i++)
    {
      (void) putchar(' ');
    }
  }
}

/*
  The following function shows the sequence header for the
  sequence with number \texttt{seqnum} in the \texttt{Multiseq}-record. 
  \texttt{showsequencelengths} is true if the option \texttt{-L} was
  set. \texttt{currentisrcmatch} is True iff if the current matches
  to be reported (if any) are reverse complemented matches.
  \texttt{seqlen} is the length of the sequence for which the header
  is shown.
*/

static void showsequenceheader(Multiseq *multiseq,
                               BOOL showsequencelengths,
                               BOOL currentisrcmatch,
                               Uint seqnum,
                               Uint seqlen)
{

  printf("%c ",FASTASEPARATOR);
  showsequencedescription(multiseq,0,seqnum);
  if(currentisrcmatch)
  {
    printf(" Reverse");
  }
  if(showsequencelengths)
  {
    printf("  Len = %lu",(Showuint) seqlen);
  }
  printf("\n");
}

/*
  The following is one of three functions to further process 
  a MUM-candidate specfied by its length, its start position
  in the subject sequence, the number of the query in which
  it matches as well as the start of the match in the query.
  The function \texttt{showmaximalmatch} simply shows the 
  relevant information as a triple of three integers.
*/

static Sint showmaximalmatch (void *info,
                              Uint matchlength,
                              Uint subjectstart,
                              /*@unused@*/ Uint seqnum,
                              Uint querystart)
{
  /*Matchprocessinfo *matchprocessinfo = (Matchprocessinfo *) info;

  if(matchprocessinfo->subjectmultiseq->numofsequences == UintConst(1)
     &&
     !matchprocessinfo->fourcolumn)
  {
    printf ("%8lu  ", (Showuint) (subjectstart+1));
  } else
  {
    PairUint pp;

    if(pos2pospair(matchprocessinfo->subjectmultiseq,&pp,subjectstart) != 0)
    {
      return -1;
    }
    printf("  ");
    showsequencedescription(matchprocessinfo->subjectmultiseq,
                            matchprocessinfo->maxdesclength,
                            pp.uint0);
    printf ("  %8lu  ",(Showuint) (pp.uint1+1));
  }
  if(matchprocessinfo->currentisrcmatch && 
     matchprocessinfo->showreversepositions)
  {
    printf ("%8lu  ", (Showuint) (matchprocessinfo->currentquerylen - 
                                  querystart));
  } else
  {
    printf ("%8lu  ", (Showuint) (querystart+1));
  }
  printf ("%8lu\n", (Showuint) matchlength);*/
  return 0;
}

/*
  The following function shows the same information as the previous
  function and additionally the sequence information.
*/

static Sint showseqandmaximalmatch (void *info,
                                    Uint matchlength,
                                    Uint subjectstart,
                                    Uint seqnum,
                                    Uint querystart)
{
  Matchprocessinfo *matchprocessinfo = (Matchprocessinfo *) info;

  (void) showmaximalmatch (info,
                           matchlength,
                           subjectstart,
                           seqnum,
                           querystart);
  if (fwrite (matchprocessinfo->subjectmultiseq->sequence + subjectstart, 
              sizeof (Uchar), 
              (size_t) matchlength,
              stdout) != (size_t) matchlength)
  {
    ERROR1 ("cannot output string of length %lu", (Showuint) matchlength);
    return -1;
  }
  printf ("\n");
  return 0;
}

/*
  The following function stores the information about a MUM-candidate
  in the next free position of the dynamic array \texttt{mumcandtab}.
*/

static Sint storeMUMcandidate (void *info,
                               Uint matchlength,
                               Uint subjectstart,
                               Uint seqnum,
                               Uint querystart)
{
  Matchprocessinfo *matchprocessinfo = (Matchprocessinfo *) info;
  MUMcandidate *mumcandptr;

  DEBUG4(3,"storeMUMcandiate %lu %lu %lu %lu\n",
            (Showuint) matchlength,
            (Showuint) subjectstart,
            (Showuint) seqnum,
            (Showuint) querystart);
  GETNEXTFREEINARRAY(mumcandptr,
                     &matchprocessinfo->mumcandtab,
                     MUMcandidate,1024);
  mumcandptr->mumlength = matchlength;
  mumcandptr->dbstart = subjectstart;
  mumcandptr->queryseq = seqnum;
  mumcandptr->querystart = querystart;
  return 0;
}

/*
  The following function searches for forward and reverse complemented
  MUM-candidates (if necessary) in the current query of length
  \texttt{querylen}. The number of the query sequence is 
  \texttt{querylen}.
*/

static Sint findmaxmatchesonbothstrands(void *info,Uint seqnum,
                                        Uchar *query,Uint querylen)
{
  Matchprocessinfo *matchprocessinfo = (Matchprocessinfo *) info;
  Processmatchfunction processmatch;
  Findmatchfunction findmatchfunction;

  if(matchprocessinfo->cmum)
  {
    processmatch = storeMUMcandidate;
    findmatchfunction = findmumcandidates;
  } else
  {
    if(matchprocessinfo->showstring)
    {
      processmatch = showseqandmaximalmatch;
    } else
    {
      processmatch = showmaximalmatch;
    }
    if(matchprocessinfo->cmumcand)
    {
      findmatchfunction = findmumcandidates;
    } else
    {
      findmatchfunction = findmaxmatches;
    }
  }
  matchprocessinfo->currentquerylen = querylen;
  if(matchprocessinfo->forward)
  {
    showsequenceheader(&matchprocessinfo->querymultiseq,
                       matchprocessinfo->showsequencelengths,
                       False,
                       seqnum,
                       querylen);
    matchprocessinfo->currentisrcmatch = False;
    if(findmatchfunction(&matchprocessinfo->stree,
                         matchprocessinfo->table,
                         matchprocessinfo->minmatchlength,
                         processmatch,
                         info,
                         query,
                         querylen,
                         seqnum) != 0)
    {
      return -1;
    }
    PROCESSREALMUMS;
  }
  if(matchprocessinfo->reversecomplement)
  {
    if(matchprocessinfo->cmum)
    {
      matchprocessinfo->mumcandtab.nextfreeMUMcandidate = 0;
    }
    showsequenceheader(&matchprocessinfo->querymultiseq,
                       matchprocessinfo->showsequencelengths,
                       True,
                       seqnum,
                       querylen);
    wccSequence(query,querylen);
    matchprocessinfo->currentisrcmatch = True;
    if(findmatchfunction(&matchprocessinfo->stree,
                         matchprocessinfo->table,
                         matchprocessinfo->minmatchlength,
                         processmatch,
                         info,
                         query,
                         querylen,
                         seqnum) != 0)
    {
      return -2;
    }
    PROCESSREALMUMS;
  }
  return 0;
}

static Sint getmaxdesclen(Multiseq *multiseq)
{
  Uint desclen, maxdesclen, seqnum;
  if(multiseq->numofsequences == 0)
  {
    ERROR0("multiple sequence contains 0 sequences");
    return -1;
  }
  maxdesclen = DESCRIPTIONLENGTH(multiseq,0);
  for(seqnum = UintConst(1); seqnum < multiseq->numofsequences; seqnum++)
  {
    desclen = DESCRIPTIONLENGTH(multiseq,seqnum);
    if(desclen > maxdesclen)
    {
      maxdesclen = desclen;
    }
  }
  return (Sint) maxdesclen;
}

Uint getmaxtextlenstree(void)
{
  return MAXTEXTLEN;
}

/*EE
  The following function constructs the suffix tree,
  initializes the \texttt{Matchprocessinfo}-record appropriately,
  initializes the dynamic array \texttt{mumcandtab} (if necessary),
  and then iterates the function \texttt{findmaxmatchesonbothstrands}
  over all sequences in \texttt{querymultiseq}. Finally, the space
  allocated for the suffix tree and the space for \texttt{mumcandtab}
  is freed.
*/

Sint procmaxmatches(MMcallinfo *mmcallinfo,Multiseq *subjectmultiseq)
{
  Matchprocessinfo matchprocessinfo;
  Uint filenum, filelen;
  Sint retcode;
  Uchar *filecontent;

  fprintf(stderr,"# construct suffix tree for sequence of length %lu\n",
           (Showuint) subjectmultiseq->totallength);
  fprintf(stderr,"# (maximum reference length is %lu)\n",
           (Showuint) getmaxtextlenstree());
  fprintf(stderr,"# (maximum query length is %lu)\n",
          (Showuint) ~((Uint)0));
  if(constructprogressstree (&matchprocessinfo.stree,
                             subjectmultiseq->sequence,
                             subjectmultiseq->totallength,
                             NULL,
                             NULL,
                             NULL) != 0)
  {
    return -1;
  }
  fprintf(stderr,"# CONSTRUCTIONTIME %s %s %.2f\n",
         &mmcallinfo->program[0],&mmcallinfo->subjectfile[0],
         getruntime());
  Uint wordsize=10;
  Uint size = pow(2,3*wordsize);
  if (size>pow(2,32))
      return -1;
  double start, finish;
  start = MPI::Wtime();
  vector<Uint*> table(size,0);
  createTable(&matchprocessinfo.stree,table,wordsize);
  finish = MPI::Wtime();
  cerr << "createTable Time: " << finish-start << endl;
  Uint total=0;
  /*for (vector<Uint*>::iterator it=table.begin();it!=table.end();++it)
  {
          cout << *it << endl;
  }
  cout << "Termina iteración" << endl;*/
  matchprocessinfo.subjectmultiseq = subjectmultiseq;
  matchprocessinfo.minmatchlength = mmcallinfo->minmatchlength;
  matchprocessinfo.showstring = mmcallinfo->showstring;
  matchprocessinfo.showsequencelengths = mmcallinfo->showsequencelengths;
  matchprocessinfo.showreversepositions = mmcallinfo->showreversepositions;
  matchprocessinfo.forward = mmcallinfo->forward;
  matchprocessinfo.fourcolumn = mmcallinfo->fourcolumn;
  matchprocessinfo.cmum = mmcallinfo->cmum;
  matchprocessinfo.cmumcand = mmcallinfo->cmumcand;
  matchprocessinfo.reversecomplement = mmcallinfo->reversecomplement;
  matchprocessinfo.table = table;
  if(mmcallinfo->cmum)
  {
    INITARRAY(&matchprocessinfo.mumcandtab,MUMcandidate);
  }
  retcode = getmaxdesclen(subjectmultiseq);
  if(retcode < 0)
  {
    return -2;
  }
  matchprocessinfo.maxdesclength = (Uint) retcode;
  for(filenum=0; filenum < mmcallinfo->numofqueryfiles; filenum++)
  {
    filecontent = (Uchar *)CREATEMEMORYMAP (mmcallinfo->queryfilelist[filenum],
                                   True, 
                                   &filelen);
    if (filecontent == NULL || filelen == 0)
    {
      ERROR2("cannot open file \"%s\" or file \"%s\" is empty",
              mmcallinfo->queryfilelist[filenum],
              mmcallinfo->queryfilelist[filenum]);
      return -3;
    }
    if (scanmultiplefastafile (&matchprocessinfo.querymultiseq, 
                               mmcallinfo->queryfilelist[filenum],
                               mmcallinfo->matchnucleotidesonly 
                                ? MMREPLACEMENTCHARQUERY 
                                : 0,
                               filecontent, filelen) != 0)
    {
      return -4;
    }
    fprintf(stderr,
	    "# matching query-file \"%s\"\n# against subject-file \"%s\"\n",
            mmcallinfo->queryfilelist[filenum],
            mmcallinfo->subjectfile);
    if (overallsequences (False,
                          &matchprocessinfo.querymultiseq,
                          (void *) &matchprocessinfo,
                          findmaxmatchesonbothstrands) != 0)
    {
      return -5;
    }
    freemultiseq(&matchprocessinfo.querymultiseq);
  }
  if(mmcallinfo->cmum)
  {
    FREEARRAY(&matchprocessinfo.mumcandtab,MUMcandidate);
  }
  freestree (&matchprocessinfo.stree);
  return 0;
}
