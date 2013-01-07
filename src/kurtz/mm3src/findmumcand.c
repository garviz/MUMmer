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
#include <omp.h>
#include <likwid.h>
#include "streedef.h"
#include "debugdef.h"
#include "spacedef.h"
#include "maxmatdef.h"

//}

/*EE
  This module contains functions to compute MUM-candidates using
  a linear time suffix tree traversal. 
*/

typedef struct
  { 
   long int  R, Q, Len, Seq;
   unsigned int  Good : 1;
   unsigned int  Tentative : 1;
  } Match_t;

/* Reallocate memory for  Q  to  Len  bytes and return a
*  pointer to the new memory.  Exit if fail. */
void *  Safe_realloc  (void * Q, size_t Len)
  {
   void  * P;

   P = realloc (Q, Len);
   if  (P == NULL)
   { 
      fprintf (stderr, "# ERROR:  realloc failed, there is not enough memory\n");
      //MPI_Finalize();
   } 

   return  P;
  }  

/* Allocate and return a pointer to  Len  bytes of memory.
*  Exit if fail. */
void *  Safe_malloc  (size_t Len)
  {
   void  * P;

   P = malloc (Len);
   if  (P == NULL)
   {
      fprintf (stderr,"# ERROR:  malloc failed, there is not enough memory\n");
      //MPI_Finalize();
   }

   return  P;
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
                                      Match_t *A,
                                      Uint *Size,
                                      Uint *N)
{
  if (loc->remain > 0 
      && loc->nextnode.toleaf
      && (querysuffix == query || loc->locstring.start == 0
			       || *(querysuffix - 1) != 
                                  subjectseq[loc->locstring.start - 1]))
  {
      if (*N >= *Size -1)
      {
          *Size = *Size * 2;
          //A = (Match_t *) Safe_realloc (A, *Size * sizeof (Match_t));
      }
      else
      {
      A[*N].R = loc->locstring.start;
      A[*N].Q = (Uint) (querysuffix-query);
      A[*N].Len = loc->locstring.length;
      A[*N].Seq = seqnum;
      fprintf(stderr,"%lu %lu %lu %lu %lu\n", (*N), A[(*N)].R, A[(*N)].Q, A[(*N)].Len, A[(*N)].Seq);
      }
      (*N)++;
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
                       Uint minmatchlength,
                       Uint chunks,
                       Processmatchfunction processmumcandidate,
                       void *processinfo,
                       SYMBOL *query,
                       Uint querylen,
                       Uint seqnum)
{
  SYMBOL *lptr, *left,
        *right, 
        *querysuffix;
  Location loc;
  int i, nthreads;
  Uint N, Size, offset;
  double start, end;
  Match_t *A;
  
  DEBUG1(2,"query of length %lu=",(Showuint) querylen);
  DEBUGCODE(2,(void) fwrite(query,sizeof(Uchar),(size_t) querylen,stdout));
  DEBUG0(2,"\n");
  start = omp_get_wtime();
#pragma omp parallel default(none) private(i,left,right,lptr,querysuffix,loc,N,A,Size,processmumcandidate,processinfo,offset) shared(stdout,chunks,query,querylen,stree,minmatchlength,seqnum,nthreads)
  { 
      likwid_markerStartRegion("Find MUMs");
      nthreads = omp_get_num_threads();
      A = (Match_t *) Safe_malloc (Size * sizeof (Match_t));
      Size = 32768;
      N = 0;
#pragma omp for schedule(runtime) nowait
      for (i=0;i<chunks;i++)
      { 
          left = query + querylen/chunks*i;
          lptr = left;
          right = query + querylen/chunks*(i+1)-1;
          lptr = left;
          likwid_markerStartRegion("ROOT");
          offset = scanprefixfromnodestree (stree, &loc, ROOT (stree), 
                                  left, right, 0);
          lptr += offset;
          likwid_markerStopRegion("ROOT");
          for (querysuffix = left; offset != -2; querysuffix++)
          {
              DEBUGCODE(2,showlocation(stdout,stree,&loc));
              fprintf(stdout,"offset=%lu\n",offset);
              likwid_markerStartRegion("MUM");
              if (loc.locstring.length >= minmatchlength)
                  checkiflocationisMUMcand(&loc,stree->text, querysuffix, query, seqnum, A, &Size, &N);
              likwid_markerStopRegion("MUM");
              if (ROOTLOCATION (&loc))
              {
                  likwid_markerStartRegion("ROOT");
                  offset = scanprefixfromnodestree (stree, &loc, ROOT (stree), 
                                      lptr + 1, right, 0);
                  if (offset > 0)
                      lptr += offset;
                  likwid_markerStopRegion("ROOT");
              }
              else
              { 
                  likwid_markerStartRegion("SL");
                  linklocstree (stree, &loc, &loc);
                  offset = scanprefixstree (stree, &loc, &loc, lptr, right, 0);
                  if (offset > 0)
                      lptr += offset;
                  likwid_markerStopRegion("SL");
              }
          }
          DEBUGCODE(2,showlocation(stdout,stree,&loc));
          while (!ROOTLOCATION (&loc) && loc.locstring.length >= minmatchlength)
          {  
              likwid_markerStartRegion("MUM");
              if (loc.locstring.length >= minmatchlength)
                  checkiflocationisMUMcand(&loc,stree->text, left, query, seqnum, A, &Size, &N);
              likwid_markerStopRegion("MUM");
              likwid_markerStartRegion("SL");
              linklocstree (stree, &loc, &loc);
              likwid_markerStopRegion("SL");
              querysuffix++;
              DEBUGCODE(2,showlocation(stdout,stree,&loc));
          }
      }
      likwid_markerStopRegion("Find MUMs");
      //fprintf(stdout,"Matches=%lu,Size=%lu,",N,Size);
  }
  end = omp_get_wtime();
  fprintf(stdout,"Threads=%d,Chunks=%d,Chunk_size=%lu,MUMTime=%f,", nthreads, chunks, (Uint) (querylen/chunks), N, (double) (end-start));
  return 0;
}
