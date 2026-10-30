# From Z to C — Appendix C: Implementation Of The Editor Specification (PDF pages 234–278)

Source: `../source/Zeditor.pdf` (Neilson, PRG-101, 1990), Appendix C, printed pp.i–xlv. Transcribed from page images.

Conventions:
- `<!-- PDF p.N / printed p.xii -->` marks each scanned page (outside the code fences; a function may continue across a marker).
- `/* [?N] */` marks a doubtful spot; N is the ID column in `corrections.csv` (IDs 601–899 for this appendix).
- Code is transcribed as printed, including apparent bugs and inconsistent names. Exception: the typewriter font regularly confuses h/b, O/D, w/v, s/e, x/r; where the intended identifier is obvious and used consistently elsewhere it is written correctly, and where the reading could change meaning it is flagged.
- Indentation and column alignment are approximate (±1 space). `/* ---- */` separators and `/* ==== */` banner rules are normalised to a fixed width.
- Source files appear in this order, each starting with a banner comment: Doc1, Doc3, Doc4, Doc6, Doc8, Doc9 implementations; main.c, read.c, write.c, globals.c, term.c, sysentryexit.c, screen.c, externglobals.c, kbdinterpret.c, utilities.c, consts.c, messages.c.

---

<!-- PDF p.234 / printed p.i -->

# Appendix C

## Implementation Of The Editor Specification

```c
                                /* IMPLEMENTATION OF DOC1 */
                              /* ========================== */

#include "/se/daven/ox/c/c2/externglobals.c"

/* ------------------------------------------------------------------------------------ */
int OP_Doc1()
{
   if       (OP==LeftMoveChar)        { OPType=LeftMove; return(LeftMoveChar_Doc1()); }
   else if (OP==RightMoveChar)       { OPType=RightMove; return(RightMoveChar_Doc1()); }
   else if (OP==LeftMoveWord)        { OPType=LeftMove; return(LeftMoveWord_Doc1()); }
   else if (OP==RightMoveWord)       { OPType=RightMove; return(RightMoveWord_Doc1()); }
   else if (OP==LeftMoveLine)        { OPType=LeftMove; return(LeftMoveLine_Doc1()); }
   else if (OP==RightMoveLine)       { OPType=RightMove; return(RightMoveLine_Doc1()); }
   else if (OP==LeftDeleteChar)      { OPType=LeftDelete; return(LeftDeleteChar_Doc1()); }
   else if (OP==RightDeleteChar)     { OPType=RightDelete; return(RightDeleteChar_Doc1()); }
   else if (OP==LeftDeleteWord)      { OPType=LeftDelete; return(LeftDeleteWord_Doc1()); }
   else if (OP==RightDeleteWord)     { OPType=RightDelete; return(RightDeleteWord_Doc1()); }
   else if (OP==LeftDeleteLine)      { OPType=LeftDelete; return(LeftDeleteLine_Doc1()); }
   else if (OP==RightDeleteLine)     { OPType=RightDelete; return(RightDeleteLine_Doc1()); }
   else if (OP==InsertChar)          { OPType=LeftInsert; return(InsertChar_Doc1()); }
   else if (OP==MoveToTop)           { OPType=LeftMove; return(MoveToTop_Doc1()); }
   else if (OP==MoveToBot)           { OPType=RightMove; return(MoveToBot_Doc1()); }
}
/* ------------------------------------------------------------------------------------ */
int Initialize_Doc1()
{
 LP=0; CP=0; RP=Max;
}
/* ------------------------------------------------------------------------------------ */
int GetArrCont(ptr)   int ptr;
{
 if    (ptr<=LP) { return(Arr[ptr]); }
 else            { return(Arr[ptr+RP-LP]); }
}
/* ------------------------------------------------------------------------------------ */
Standardize_Doc1()
{
 if      (LP>CP) { while (LP>CP) { Arr[RP]=Arr[LP]; RP--; LP--; } }
 else if (LP<CP) { while (LP<CP) { Arr[LP+1]=Arr[RP+1]; RP++; LP++; } }
}
/* ------------------------------------------------------------------------------------ */
int RightMoveChar_Doc1()
{
 if (CP!=Max+LP-RP) { CP++; return(OK); }
 else               { return(Bot); }
}
/* ------------------------------------------------------------------------------------ */
int LeftMoveChar_Doc1()
{
 if (CP!=0) { CP--; return(OK); }
 else       { return(Top); }
}
/* ------------------------------------------------------------------------------------ */
```

<!-- PDF p.235 / printed p.ii -->

```c
int RightMoveWord_Doc1()
{
 if (CP!=Max+LP-RP) { if       (GetArrCont(CP+1)==nl) { CP++; }
                      else if (GetArrCont(CP+1)==sp) { RMWSWord(); }
                      else                           { RMNWSWord(); }
                      return(OK);
                    }
 else               { return(Bot); }
}
/* ------------------------------------------------------------------------------------ */
RMWSWord()
{
 while (CP<Max+LP-RP && GetArrCont(CP+1)==sp) { CP++; }
}
/* ------------------------------------------------------------------------------------ */
RMNWSWord()
{
 while (CP<Max+LP-RP && GetArrCont(CP+1)!=sp && GetArrCont(CP+1)!=nl) { CP++; }
}
/* ------------------------------------------------------------------------------------ */
int LeftMoveWord_Doc1()
{
 if (CP!=0) { if       (GetArrCont(CP)==nl) { CP--; }
              else if (GetArrCont(CP)==sp) { LMWSWord(); }
              else                         { LMNWSWord(); }
              return(OK);
            }
 else       { return(Top); }
}
/* ------------------------------------------------------------------------------------ */
LMWSWord()
{
 while (CP>0 && GetArrCont(CP)==sp) { CP--; }
}
/* ------------------------------------------------------------------------------------ */
LMNWSWord()
{
 while (CP>0 && GetArrCont(CP)!=sp && GetArrCont(CP)!=nl) { CP--; }
}
/* ------------------------------------------------------------------------------------ */
int RightMoveLine_Doc1()
{
 if    (CP!=Max+LP-RP) { if (GetArrCont(CP+1)==nl)
                                CP++;
                         else
                                while (CP!=Max+LP-RP && GetArrCont(CP+1)!=nl) { CP++; }
                         return(OK);
                       }
 else                  { return(Bot); }
}
/* ------------------------------------------------------------------------------------ */
int LeftMoveLine_Doc1()
{
 if (CP!=0) { if (GetArrCont(CP)==nl) CP--;
              else                    while (CP!=0 && GetArrCont(CP)!=nl) { CP--; }
              return(OK);
            }
 else       { return(Top); }
}
/* ------------------------------------------------------------------------------------ */
int RightDeleteChar_Doc1()
{
 Standardize_Doc1(); if    (RP!=Max) { RP++; return(OK); } /* [?601] */
                     else            { return(Bot); } /* [?602] */
```

<!-- PDF p.236 / printed p.iii -->

```c
}
/* ------------------------------------------------------------------------------------ */
int LeftDeleteChar_Doc1()
{
 Standardize_Doc1(); if    (LP!=0) { LP--; CP--; return(OK); }
                     else          { return(Top); }
}
/* ------------------------------------------------------------------------------------ */
int RightDeleteWord_Doc1()
{
 Standardize_Doc1();
 if (RP!=Max) { if       (Arr[RP+1]==nl) RP++;
                else if (Arr[RP+1]==sp) while (RP!=Max && Arr[RP+1]==sp) { RP++; }
                else                    while (RP!=Max && Arr[RP+1]!=nl && Arr[RP+1]!=sp)
                                                                       { RP++; }
                return(OK);
              }
 else         { return(Bot); }
}
/* ------------------------------------------------------------------------------------ */
int LeftDeleteWord_Doc1()
{
 Standardize_Doc1();
 if (LP!=0) { if       (Arr[CP]==nl) CP--;
              else if (Arr[CP]==sp) while (CP!=0 && Arr[CP]==sp) { CP--; }
              else                  while (CP!=0 && Arr[CP]!=nl && Arr[CP]!=sp) { CP--; }
              LP=CP; return(OK);
            }
 else       { return(Top); }
}
/* ------------------------------------------------------------------------------------ */
int RightDeleteLine_Doc1()
{
 Standardize_Doc1();
 if (RP!=Max) { if    (Arr[RP+1]==nl) RP++;
                else                  while (RP!=Max && Arr[RP+1]!=nl) { RP++; }
                return(OK);
              }
 else         { return(Bot); }
}
/* ------------------------------------------------------------------------------------ */
int LeftDeleteLine_Doc1()
{
  Standardize_Doc1();
 if (LP!=0) { if    (Arr[LP]==nl) LP--;
              else                while (LP!=0 && Arr[LP]!=nl) { LP--; }
              CP=LP; return(OK);
            }
 else       { return(Top); }
}
/* ------------------------------------------------------------------------------------ */
int InsertChar_Doc1()
{
 int ptr=CP;   int count=0;
 Standardize_Doc1();
 if      (LP!=RP && OPChar!=TAB) { LP++; CP++; Arr[LP]=OPChar; return(OK); }
 else if (LP!=RP && OPChar==TAB) { while (ptr!=0 && Arr[ptr]!=nl) { count++; ptr--; }
                                   count=tabstop-(count%tabstop); /* [?603] */
                                   while (count!=0 && LP!=RP) { Arr[LP+1]=sp;
                                                                 CP++; LP++; count--;
                                                               }
                                   return(OK);
                                 }
 else                            { return(Full); }
```

<!-- PDF p.237 / printed p.iv -->

```c
}
/* ------------------------------------------------------------------------------------ */
int MoveToTop_Doc1()
{
 if    (CP!=0) { CP=0; return(OK); }
 else          { return(Top); }
}
/* ------------------------------------------------------------------------------------ */
int MoveToBot_Doc1()
{
 if    (CP!=Max+LP-RP) { CP=(Max+LP-RP); return(OK); } /* [?604] */
 else                  { return(Bot); }
}
/* ------------------------------------------------------------------------------------ */




                              /* IMPLEMENTATION OF DOC3 */
                            /* ========================== */

#include "/se/daven/ox/c/c2/externglobals.c"

/* ------------------------------------------------------------------------------------ */
int OP_Doc3()
{
 int prevCP=CP;   int prevLP=LP;   int prevRP=RP;   int rep=OP_Doc1();
 Update_Doc3(prevCP,prevLP,prevRP); return(rep);
}
/* ------------------------------------------------------------------------------------ */
int Initialize_Doc3()
{
 Initialize_Doc1(); Startln=0; Endln=0; CurX=1; CurY=1; DocNL=0; WSRem=0; NLRem=0;
}
/* ------------------------------------------------------------------------------------ */
SetStartln()
{
 Startln=CP; while (Startln>0 && GetArrCont(Startln)!=nl) { Startln--; }
}
/* ------------------------------------------------------------------------------------ */
SetEndln()
{
 Endln=CP; while (Endln<Max+LP-RP && GetArrCont(Endln+1)!=nl) { Endln++; }
}
/* ------------------------------------------------------------------------------------ */
Update_Doc3(prevCP,prevLP,prevRP)   int prevCP;   int prevLP;   int prevRP;
{
 int NumNL;   WSRem=0; NLRem=0;
 if (OPType!=NoMove)
       { SetStartln(); SetEndln(); CurX=CP-Startln+1;
         if       (OPType==LeftInsert)  { NumNL=NLCountArr(prevCP,CP); CurY=CurY+NumNL;
                                          DocNL=DocNL+NumNL;
                                          }
         else if (OPType==RightInsert) { DocNL=DocNL+NLCountArr(RP,LP-prevLP+prevRP); }
         else if (OPType==LeftDelete)  { NumNL=NLCountArr(CP,prevCP);  DocNL=DocNL-NumNL;
                                          CurY=CurY-NumNL;
                                          }
         else if (OPType==RightDelete) { Standardize_Doc1();
                                          DocNL=DocNL-NLCountArr(LP-prevLP+prevRP,RP);
                                          }
```

<!-- PDF p.238 / printed p.v -->

```c
         else if (OPType==LeftMove)    { if (CP==0) { CurY=1; }
                                         else       { CurY=CurY-NLCountArrCont(CP,prevCP);}
                                        }
         else if (OPType==RightMove)   { if (CP==Max+LP-RP)
                                                { CurY=DocNL+1; }
                                         else
                                                { CurY=CurY+NLCountArrCont(prevCP,CP); }
                                        }
         RemTrailWS(prevCP); RemTrailNL();
       }
}
/* ------------------------------------------------------------------------------------ */
int NLCountArr(first,last)   register int first;   int last;
{
 int NumNL=0;
 while (first!=last) { first++; if (Arr[first]==nl) { NumNL++; } }
 return(NumNL);
}
/* ------------------------------------------------------------------------------------ */
int NLCountArrCont(first,last)   register int first;   int last;
{
 int NumNL=0;
 while (first!=last) { first++; if (GetArrCont(first)==nl) { NumNL++; } }
 return(NumNL);
}
/* ------------------------------------------------------------------------------------ */
RemTrailWS(prevCP)   int prevCP;
{
 int tempCP=CP;   int tempEndln=Endln;   int prevEndln;
 CP=prevCP; SetEndln(); prevEndln=Endln; CP=tempCP; Endln=tempEndln;
 if (OPType=LeftMove || OPType==RightMove || OPType==LeftInsert || OPType==RightInsert) /* [?605] */
       { if (prevEndln==Endln)
               { if (Endln!=CP && GetArrCont(Endln)==sp)
                      { CP=Endln; Standardize_Doc1(); CP=tempCP;
                        while (Endln!=CP && Arr[Endln]==sp) { Endln--; LP--; WSRem++; }
                      }
               }
         else
               { if (prevEndln!=0 && GetArrCont(prevEndln)==sp)
                      { CP=prevEndln; Standardize_Doc1(); CP=tempCP;
                        while (LP!=0 && Arr[LP]==sp) { LP--; WSRem++; }
                        if (CP>LP) { CP=CP-WSRem; Startln=Startln-WSRem;
                                     Endln=Endln-WSRem;
                                    }
                      }
               }
       } /* [?606] */
}
/* ------------------------------------------------------------------------------------ */
RemTrailNL()
{
 int tempCP=CP;
 if (OPType==LeftMove || OPType==RightInsert)
       { if (CP!=Max+LP-RP && GetArrCont(Max+LP-RP)==nl)
                { CP=Max+LP-RP; Standardize_Doc1(); CP=tempCP;
                  while (LP!=CP && Arr[LP]==nl)  { LP--; DocNL--; NLRem++;}
                }
       }
}
/* ------------------------------------------------------------------------------------ */
```

<!-- PDF p.239 / printed p.vi -->

```c



                                  /* IMPLEMENTATION OF DOC4 */
                                /* ========================== */

#include "/se/daven/ox/c/c2/externglobals.c"

/* ------------------------------------------------------------------------------------ */
int OP_Doc4()
{
 int rep;
 if       (OP==CursorUpLine)    { rep=CursorUpLine_Doc4(); OPType=LeftMove; }
 else if (OP==CursorUpPage)    { rep=CursorUpPage_Doc4(); OPType=LeftMove; }
 else if (OP==CursorDownLine)  { rep=CursorDownLine_Doc4(); OPType=RightMove; }
 else if (OP==CursorDownPage)  { rep=CursorDownPage_Doc4(); OPType=RightMove; }
 else if (OP==CursorLeftChar)  { rep=CursorLeftChar_Doc4(); OPType=LeftMove; }
 else if (OP==CursorRightChar) { rep=CursorRightChar_Doc4(); OPType=RightMove; }
 else                          { rep=OP_Doc3(); Update_Doc4(); }
 return(rep);
}
/* ------------------------------------------------------------------------------------ */
int Initialize_Doc4()
{
 Initialize_Doc3(); WSIns=0; NLIns=0;
}
/* ------------------------------------------------------------------------------------ */
Update_Doc4()
{
 WSIns=0; NLIns=0;
}
/* ------------------------------------------------------------------------------------ */
int CursorUpLine_Doc4()
{
 return(CursorUp(1));
}
/* ------------------------------------------------------------------------------------ */
int CursorUpPage_Doc4()
{
 return(CursorUp(PageHeight)); /* [?607] */
}
/* ------------------------------------------------------------------------------------ */
int CursorUp(y)   int y;
{
 int prevCP=CP;   int prevLP=LP;   int prevRP=RP;   int prevCurX=CurX;   int prevCurY=CurY;
 int prevStartln=Startln;    int prevEndln=Endln;    int prevOP=OP;      int cumWSRem=0;
 int cumNLRem=0;             int rep;
 WSIns=0; NLIns=0;
 if (CurY!=1)
       { OP=LeftMoveLine;
         while (CurY!=prevCurY-y && CP!=0) { OP_Doc3(); UpdatecumWSNL(&cumWSRem,&cumNLRem);}
         if       (prevCurX<=Endln-Startln+1)
                    { CurX=prevCurX; CP=Startln+CurX-1; rep=OK; }
         else if (prevCurX>Endln-Startln+1 && LP+prevCurX-1-Endln+Startln<=RP)
                    { CP=Endln; CurX=Endln-Startln+1; OP=InsertChar; OPChar=sp;
                      while (CurX!=prevCurX) { OP_Doc3(); WSIns++;
                                               UpdatecumWSNL(&cumWSRem,&cumNLRem);
                                             }
                      rep=OK;
                    }
         else
                    { CP=prevCP; LP=prevLP; RP=prevRP; CurX=prevCurX; CurY=prevCurY;
                      Startln=prevStartln; Endln=prevEndln; rep=Full;
                    }
```

<!-- PDF p.240 / printed p.vii -->

```c
         WSRem=cumWSRem; NLRem=cumNLRem; OP=prevOP; return(rep);
       }
 else
       { Update_Doc3(prevCP,prevLP,prevRP); Update_Doc4(); return(TopLine); }
}
/* ------------------------------------------------------------------------------------ */
int CursorDownLine_Doc4()
{
 return(CursorDown(1));
}
/* ------------------------------------------------------------------------------------ */
int CursorDownPage_Doc4()
{
 return(CursorDown(PageHeight));
}
/* ------------------------------------------------------------------------------------ */
int CursorDown(y)   int y;
{
 int prevCP=CP;   int prevLP=LP;   int prevRP=RP;   int prevCurX=CurX;   int prevCurY=CurY;
 int prevStartln=Startln;   int prevEndln=Endln;   int prevOP=OP;      int cumWSRem=0;
 int cumNLRem=0;            int rep;
 WSIns=0; NLIns=0;  OP=RightMoveLine;
 while (CurY!=prevCurY+y && CP!=Max+LP-RP)
            { OP_Doc3(); UpdatecumWSNL(&cumWSRem,&cumNLRem);}
 if (CurY==prevCurY+y && LP+prevCurX-Endln+Startln-1<=RP)
            { if (prevCurX<=Endln-Startln+1)
                        { CurX=prevCurX; CP=Startln+CurX-1; }
              else
                        { CurX=Endln-Startln+1; CP=Endln; OP=InsertChar; OPChar=sp;
                          while (CurX!=prevCurX) { OP_Doc3(); WSIns++;
                                                   UpdatecumWSNL(&cumWSRem,&cumNLRem);
                                                 }
                        }
              rep=OK;
            }
 else if (CurY!=prevCurY+y && LP+prevCurY+y-DocNL-1+prevCurX-1<=RP)
            { OP=InsertChar; OPChar=nl;
              while (CurY!=prevCurY+y) { OP_Doc3(); NLIns++;
                                         UpdatecumWSNL(&cumWSRem,&cumNLRem);
                                       }
              OPChar=sp; while (CurX!=prevCurX) { OP_Doc3(); WSIns++;
                                                  UpdatecumWSNL(&cumWSRem,&cumNLRem);
                                                }
              rep=OK;
            }
 else
            { CP=prevCP; LP=prevLP; RP=prevRP; CurX=prevCurX; CurY=prevCurY;
              Startln=prevStartln; Endln=prevEndln; rep=Full;
            }
 WSRem=cumWSRem; OP=prevOP; return(rep);

}
/* ------------------------------------------------------------------------------------ */
int CursorLeftChar_Doc4()
{
 int rep;
 WSIns=0; NLIns=0; OP=LeftMoveChar; rep=OP_Doc3(); OP=CursorLeftChar; return(rep);
}
/* ------------------------------------------------------------------------------------ */
int CursorRightChar_Doc4()
{
 int rep;
 WSIns=0; NLIns=0;
 if    (CP!=Endln) { OP=RightMoveChar; rep=OP_Doc3(); }
```

<!-- PDF p.241 / printed p.viii -->

```c
 else              { OP=InsertChar; OPChar=sp; rep=OP_Doc3(); WSIns++; }
 OP=CursorRightChar; return(rep);
}
/* ------------------------------------------------------------------------------------ */
UpdatecumWSNL(cumWSRem,cumNLRem)  int *cumWSRem;  int *cumNLRem;
{
 *cumWSRem=(*cumWSRem)+WSRem; *cumNLRem=(*cumNLRem)+NLRem;
}
/* ------------------------------------------------------------------------------------ */




                                  /* IMPLEMENTATION OF DOC6 */
                                /* ========================== */

#include "/se/daven/ox/c/c2/externglobals.c"

/* ------------------------------------------------------------------------------------ */
int OP_Doc6()
{
 int prevCP=CP;   int prevLP=LP;   int prevRP=RP;  int rep;
 if       (OP==Mark)  { OPType=NoMove; rep=Mark_Doc6(); Update_Doc3(prevCP,prevLP,prevRP);
                        Update_Doc4();
                      }
 else if (OP==Lift)  { OPType=NoMove; rep=Lift_Doc6(); Update_Doc3(prevCP,prevLP,prevRP);
                        Update_Doc4(); }
 else if (OP==Cut)   { if (CP>MP) { OPType=LeftDelete; } else { OPType=RightDelete; }
                        rep=Cut_Doc6(); Update_Doc3(prevCP,prevLP,prevRP); Update_Doc4();
                      }
 else if (OP==Paste) { OPType=LeftInsert;
                        rep=Paste_Doc6(); Update_Doc3(prevCP,prevLP,prevRP); Update_Doc4();
                      }
 else                { rep=OP_Doc4(); Update_Doc6(prevCP); }
 return(rep);
}
/* ------------------------------------------------------------------------------------ */
int Initialize_Doc6()
{
 Initialize_Doc4(); PP=0; MP=(-1);
}
/* ------------------------------------------------------------------------------------ */
Update_Doc6(prevCP)   int prevCP;
{
 if ((OPType!=NoMove && OPType!=LeftMove && OPType!=RightMove) || MP>Max+LP-RP)
       { MP=(-1); }
 else
       { if       (prevCP<=MP && CP<=MP) { MP=MP-WSRem+WSIns; }
         else if (prevCP<=MP && CP>=MP) { MP=MP-WSRem; }
         else if (prevCP>=MP && CP<=MP) { MP=MP+WSIns; }
       }
}
/* ------------------------------------------------------------------------------------ */
int Mark_Doc6()
{
 MP=CP; return(OK);
}
/* ------------------------------------------------------------------------------------ */
int Lift_Doc6()
{
```

<!-- PDF p.242 / printed p.ix -->

```c
 if    (CP!=MP && MP!=(-1)) { CopyMTextPBuff(); return(OK); }
 else                       { return(NoTextMarked); }
}
/* ------------------------------------------------------------------------------------ */
CopyMTextPBuff()
{
 int MPptr; PP=0;
 if      (CP<MP) { MPptr=CP;
                   while (MPptr!=MP) { MPptr++; PP++; PArr[PP]=GetArrCont(MPptr); }
                       } /* [?608] */
 else if (CP>MP) { MPptr=MP;
                   while (MPptr!=CP) { MPptr++; PP++; PArr[PP]=GetArrCont(MPptr); } /* [?609] */
                       } /* [?610] */
}
/* ------------------------------------------------------------------------------------ */
int Cut_Doc6()
{
 if (MP!=(-1) && MP!=CP) { CopyMTextPBuff(); RemMText(); return(OK); }
 else                    { return(NoTextMarked); }
}
/* ------------------------------------------------------------------------------------ */
RemMText()
{
 Standardize_Doc1(); if       (MP<CP) { LP=MP; CP=MP; }
                     else if (MP>CP) { RP=RP+MP-LP; }
 MP=(-1);
}
/* ------------------------------------------------------------------------------------ */
int Paste_Doc6()
{
 int PPptr;
 if      (PP==0)
           { return(PBuffEmpty); }
 else if (PP!=0 && PP>RP-LP)
           { return(Full); }
 else
           { Standardize_Doc1(); MP=CP; PPptr=0;
             while (PPptr!=PP) { PPptr++; LP++; CP++; Arr[LP]=PArr[PPptr]; }
             return(OK); /* [?611] */
           }
}
/* ------------------------------------------------------------------------------------ */




                                  /* IMPLEMENTATION OF DOC8 */
                                /* ========================== */

#include "/se/daven/ox/c/c2/externglobals.c"
#include <stdio.h>
#include <sys/types.h>
#include <sys/stat.h>

/* ------------------------------------------------------------------------------------ */
int OP_Doc8()
{
 int prevCP=CP;   int prevLP=LP;   int prevRP=RP;   int rep;
 if (EState==State_Doc)
      { if       (OP==DownSearch) { OPType=RightMove; rep=DownSearch_Doc8();
```

<!-- PDF p.243 / printed p.x -->

```c
                                   Update_Doc3(prevCP,prevLP,prevRP);
                                    Update_Doc4(); Update_Doc6(prevCP);
                                 }
        else if (OP==UpSearch)   { OPType=LeftMove; rep=UpSearch_Doc8();
                                   Update_Doc3(prevCP,prevLP,prevRP);
                                   Update_Doc4(); Update_Doc6(prevCP);
                                 }
        else if (OP==Replace)    { OPType=RightDelete;
                                   rep=Replace_Doc8(&prevCP,&prevLP,&prevRP);
                                   OPType=LeftInsert; Update_Doc3(prevCP,prevLP,prevRP);
                                   Update_Doc4(); Update_Doc6(prevCP);
                                 }
        else if (OP==Quote)      { rep=Quote_StateDoc(); Update_Doc3(prevCP,prevLP,prevRP);
                                   Update_Doc4(); Update_Doc6(prevCP);
                                 }
        else                     { rep=OP_Doc6(); Update_Doc8(); }
        return(rep);
      }
 else
      { if       (OP==InsertChar)      { rep=InsertChar_Quote(); }
        else if (OP==LeftMoveChar)    { rep=LeftMoveChar_Quote(); }
        else if (OP==CursorLeftChar)  { rep=LeftMoveChar_Quote(); }
        else if (OP==RightMoveChar)   { rep=RightMoveChar_Quote(); }
        else if (OP==CursorRightChar) { rep=RightMoveChar_Quote(); }
        else if (OP==LeftDeleteChar)  { rep=LeftDeleteChar_Quote(); }
        else if (OP==RightDeleteChar) { rep=RightDeleteChar_Quote(); }
        else if (OP==DownSearch)      { OPType=RightMove; rep=DownSearch_Doc8();
                                         Update_Doc3(prevCP,prevLP,prevRP);
                                         Update_Doc4(); Update_Doc6(prevCP);
                                      }
        else if (OP==UpSearch)        { OPType=LeftMove; rep=UpSearch_Doc8();
                                         Update_Doc3(prevCP,prevLP,prevRP);
                                         Update_Doc4(); Update_Doc6(prevCP);
                                      }
        else if (OP==Replace)         { OP=RightDelete;
                                        rep=Replace_Doc8(&prevCP,&prevLP,&prevRP);
                                        OPType=LeftInsert;
                                        Update_Doc3(prevCP,prevLP,prevRP);
                                        Update_Doc4(); Update_Doc6(prevCP);
                                      }
        else if (OP==Quote)           { rep=Quote_StateQuote();
                                        Update_Doc3(prevCP,prevLP,prevRP);
                                        Update_Doc4(); Update_Doc6(prevCP);
                                      }
        else                          { Update_Doc3(prevCP,prevLP,prevRP); Update_Doc4();
                                        Update_Doc6(prevCP); rep=IllegalEditOp;
                                      }

        return(rep);
      }
}
/* ------------------------------------------------------------------------------------ */
int Initialize_Doc8()
{
 Initialize_Doc6(); SP=0; MatchedLength=0; RpP=0; EState=State_Doc; DocChanged=FALSE;
}
/* ------------------------------------------------------------------------------------ */
Update_Doc8()
{
 if (OPType!=NoMove && OPType!=LeftMove && OPType!=RightMove)
       { if (DocChanged==FALSE) { PromptDisplayed=FALSE; }
         DocChanged=TRUE;
       } /* [?612] */
}
/* ------------------------------------------------------------------------------------ */
```

<!-- PDF p.244 / printed p.xi -->

```c
int DownSearch_Doc8()
{
 int prevCP=CP;   int matched=FALSE;   char schstring[QMax];
 if (EState==State_Quote) { CopyQBuffSBuff(); EState=State_Doc; }
 CopySBuffToString(schstring);
 if    (SP!=0) { SetPromptMsg(schstring); PromptMessage(SearchingDownFor);
                  while (CP<Max+LP-RP && Not(matched) && NoInterrupt)
                           { CP++; CheckForMatch(&matched); }
                  if (matched) { PromptMessage(Found); return(OK); } /* [?613] */
                  else         { CP=prevCP; SetPromptMsg(schstring); return(NotFound); }
                }
 else          { return(SBuffEmpty); }
}
/* ------------------------------------------------------------------------------------ */
int UpSearch_Doc8()
{
 int matched=FALSE;   int prevCP=CP;   char schstring[QMax];
 if (EState==State_Quote) { CopyQBuffSBuff(); EState=State_Doc; }
 CopySBuffToString(schstring);
 if    (SP!=0) { SetPromptMsg(schstring); PromptMessage(SearchingUpFor);
                  while (CP>0 && Not(matched) && NoInterrupt)
                           { CP--; CheckForMatch(&matched); }
                  if (matched) { PromptMessage(Found); return(OK); }
                  else         { CP=prevCP; SetPromptMsg(schstring); return(NotFound); }
                }
 else          { return(SBuffEmpty); }
}
/* ------------------------------------------------------------------------------------ */
CheckForMatch(matched)   int *matched; /* [?614] */
{
 int SPptr=0;   int Docptr=0; int lastmatchOK=TRUE;
 while (SPptr!=SP && CP+Docptr<Max+LP-RP && lastmatchOK)
         { lastmatchOK=CharMatched(GetArrCont(CP+Docptr+1),&SPptr); SPptr++; Docptr++; } /* [?615] */
 if (SPptr==SP && lastmatchOK) { *matched=TRUE; MatchedLength=Docptr; } /* [?616] */
}
/* ------------------------------------------------------------------------------------ */
int CharMatched(c,ptr)   char c;   int *ptr;
{
 int prevptr=(*ptr);   int between=FALSE;   int Notflag=FALSE;   int min;   int max;
 if       (SArr[(*ptr)+1]=='.')  { return(TRUE); }
 else if (SArr[(*ptr)+1]=='\\') { (*ptr)++; return((*ptr)!=SP && SArr[(*ptr)+1]==c); }
 else if (SArr[(*ptr)+1]=='^')  { (*ptr)++; return((*ptr)!=SP && SArr[(*ptr)+1]!=c); } /* [?617] */
 else if (SArr[(*ptr)+1]=='[')  { while ((*ptr)!=SP && SArr[(*ptr)+1]!=']') { (*ptr)++; } /* [?618] */
                                  if ((*ptr)==SP) { return(FALSE); }
                                  if (SArr[prevptr+2]=='^') { Notflag=TRUE; prevptr++; } /* [?619] */
                                  if ((*ptr)-prevptr==4 && SArr[(*ptr)-1]=='-')
                                       { min=SArr[(*ptr)-2]; max=SArr[*ptr];
                                         between=(c>=min && c<=max);
                                       }
                                  else
                                       {
                                         while (prevptr+1!=(*ptr) && Not(between))
                                            { prevptr++; between=(c==SArr[prevptr+1]); }
                                       }
                                  if    (Notflag) { return(Not(between)); }
                                  else            { return(between); }
                                }
 else                           { return(SArr[(*ptr)+1]==c); }
}
/* ------------------------------------------------------------------------------------ */
int Replace_Doc8(prevCP,prevLP,prevRP)   int *prevCP;   int *prevLP;   int *prevRP;
{
 int ptr=0;   int matched;   char schstring[QMax];   char rplstring[QMax];
 if (EState==State_Quote) { CopyQBuffRpBuff(); EState=State_Doc; }
```

<!-- PDF p.245 / printed p.xii -->

```c
 CheckForMatch(&matched);
 if       (matched && RpP-MatchedLength<=RP-LP)
            { Standardize_Doc1(); CopySBuffToString(schstring);
              CopyRBuffToString(rplstring); SetPromptMsg(schstring); /* [?620] */
              PromptMessage(Replaced); SetPromptMsg(rplstring); PromptMessage(With);
              RP=RP+MatchedLength; Update_Doc3(*prevCP,*prevLP,*prevRP); Update_Doc4();
              Update_Doc6(*prevCP,*prevLP,*prevRP);
              *prevCP=CP; *prevLP=LP; *prevRP=RP;
              while (ptr!=RpP) { LP++; ptr++; Arr[LP]=RpArr[ptr]; }
              CP=LP; DocChanged=TRUE; return(OK);
            }
 else if (matched && RpP-SP>RP-LP)
            { return(Full); }
 else
            { CopySBuffToString(schstring); SetPromptMsg(schstring);
              return(NotMatched);
            }
}
/* ------------------------------------------------------------------------------------ */
int Quote_StateDoc()
{
 QP=0; QCP=0; EState=State_Quote; PromptMessage(ShowQuotePrompt); return(OK);
}
/* ------------------------------------------------------------------------------------ */
int Quote_StateQuote()
{
 int rep;
 PromptCur=strlen(QuotePrompt)+QP+1;
 if (PromptCur>WinWidth-1) { PromptCur=WinWidth-1; }
 EState=State_Doc;
 if       (QArrMatchedWith("abort")) { Abort_Quote(); }
 else if (QArrMatchedWith("q"))     { return(Quit_Quote()); }
 else if (QArrMatchedWith("s"))     { return(Save_Quote()); }
 else if (QArrPrefixedBy("w "))     { return(Write_Quote()); }
 else if (QArrPrefixedBy("a "))     { return(Append_Quote()); }
 else if (QArrPrefixedBy("i "))     { return(Input_Quote()); }
 else if (QArrPrefixedBy("!"))      { return(Escape_Quote()); }
 else                               { return(MoveLineNumberOrError_Quote()); }
}
/* ------------------------------------------------------------------------------------ */
Abort_Quote()
{
 PromptMessage(EditAborted); SysExit(OK);
}
/* ------------------------------------------------------------------------------------ */
Quit_Quote() /* [?621] */
{
 int rep;   OP=Quit;
 if    (DocChanged) { if (Backup==TRUE) { WriteBackupFile(); }
                      rep=(WriteToStore(FName,"w",1,Max+LP-RP));
                      if    (rep==OK) { SysExit(rep); }
                      else            { return(rep); } /* [?622] */
                    }
 else               { PromptMessage(DocNotChanged); SysExit(OK); }
}
/* ------------------------------------------------------------------------------------ */
Save_Quote()
{
 int rep;  OP=Save;
 if    (DocChanged) { if (Backup==TRUE) { WriteBackupFile(); }
                      rep=(WriteToStore(FName,"w",1,Max+LP-RP)); DocChanged=FALSE;
                      return(rep);
                    }
 else               { return(DocNotChanged); }
```

<!-- PDF p.246 / printed p.xiii -->

```c
}
/* ------------------------------------------------------------------------------------ */
Write_Quote()
{
 char filename[QMax];   OP=Write;
 if   (MP!=(-1) && MP!=CP) { CopyQBuffToString(filename,2); SysTranslate(filename); /* [?623] */
                             PromptCur=1;
                             if    (MP<CP) { return(WriteToStore(filename,"w",MP+1,CP)); }
                             else          { return(WriteToStore(filename,"w",CP+1,MP)); }
                           }
 else                      { return(NoTextMarked); }
}
/* ------------------------------------------------------------------------------------ */
int Append_Quote()
{
 char filename[QMax];   OP=Append;
 if   (MP!=(-1) && MP!=CP) { CopyQBuffToString(filename,2); SysTranslate(filename);
                             PromptCur=1;
                             if    (MP<CP) { return(WriteToStore(filename,"a",MP+1,CP)); }
                             else          { return(WriteToStore(filename,"a",CP+1,MP)); }
                           }
 else                      { return(NoTextMarked); }
}
/* ------------------------------------------------------------------------------------ */
int Input_Quote()
{
 struct stat stbuf;    char filename[QMax];    int ctrlfound=FALSE;    int rep;
 OP=Input; OPType=LeftInsert; CopyQBuffToString(filename,2); SysTranslate(filename);
 if (FileExists(filename,&stbuf))
       { if (NotDirectory(&stbuf))
              { if (ReadPermission(filename))
                      { rep=(ReadFromStore(filename,&stbuf,&ctrlfound));
                        if (ctrlfound) { PromptMessage(CntrlFound); }
                        if (rep==OK) { DocChanged=TRUE; }
                        return(rep);
                      }
                else
                      { SetPromptMsg(filename); return(NoReadPermission); }
              }
         else
              { SetPromptMsg(filename); return(Directory); }
       }
 else
       { SetPromptMsg(filename); return(FileNotExist); }
}
/* ------------------------------------------------------------------------------------ */
int Escape_Quote()
{
 char command[QMax];   int c='\0';
 OP=Escape; CopyQBuffToString(command,1); /* [?624] */
 if (strlen(command)!=0)
       { PosImage(); SetSysCursor(); CursorToNextLine(); ResetTerminal();
         system(command); GetTermCapAndSetWin();  ReadTermMode(); SetTerminal();
         PromptMessage(HitKeyToResume); while (c!=nl) { c=GetNextChar(); }
         RefreshDisplay_Doc9(); return(OK);
       } /* [?625] */
 else
       { return(NoCommandGiven); }
}
/* ------------------------------------------------------------------------------------ */
int MoveLineNumberOrError_Quote()
{
 int numstring[QMax];   int lineX;   int prevCP=CP;
 CopyQBuffToString(numstring,0);
```

<!-- PDF p.247 / printed p.xiv -->

```c
 if (CnvStringToNum(numstring,&lineX))
       { if (lineX>DocNL+1) { lineX=DocNL+1; }
         if    (lineX<CurY) { lineX=CurY-lineX; OP=LeftMoveLine; }
         else               { lineX=lineX-CurY; OP=RightMoveLine; }
         while (lineX!=0) { OP_Doc1(); lineX--; }
         OP=LeftMoveLine; OP_Doc1();
         if (CP>prevCP) { OPType=RightMove; } else { OPType=LeftMove; }
         OP=MoveLineNumberOrError; PromptDisplayed=FALSE; PosImage(); return(OK); /* [?626] */
       }
 else
       { OP=MoveLineNumberOrError; return(QuoteError); }
}
/* ------------------------------------------------------------------------------------ */
int InsertChar_Quote()
{
 int ptr=QP;
 if   (QP!=QMax)
          { if    (OPChar!=TAB) { while (ptr!=QCP) { QArr[ptr+1]=QArr[ptr]; ptr--; }
                                  QArr[QCP+1]=OPChar; QCP++; QP++;
                                  return(OK);
                                 }
            else                { return(IllegalQuoteChar); }
          }
 else
          { return(FullQuote); }
}
/* ------------------------------------------------------------------------------------ */
int LeftMoveChar_Quote()
{
 if   (QCP!=0) { QCP--; return(OK); } /* [?627] */
 else          { return(TopQuote); }
}
/* ------------------------------------------------------------------------------------ */
int RightMoveChar_Quote()
{
 if   (QCP!=QP) { QCP++; return(OK); }
 else           { return(BotQuote); } /* [?628] */
}
/* ------------------------------------------------------------------------------------ */
int LeftDeleteChar_Quote()
{
 int ptr=QCP;
 if   (QCP!=0) { while (ptr!=QP) { QArr[ptr]=QArr[ptr+1]; ptr++; }
                 QCP--; QP--; return(OK); /* [?629] */
               }
 else          { return(TopQuote); }
}
/* ------------------------------------------------------------------------------------ */
int RightDeleteChar_Quote()
{
 int ptr=QCP+1;
 if   (QCP!=QP) { while (ptr!=QP) { QArr[ptr]=QArr[ptr+1]; ptr++; }
                  QP--; return(OK);
                }
 else           { return(BotQuote); }
}
/* ------------------------------------------------------------------------------------ */
int QArrPrefixedBy(target)   char target[];
{
 int prefixed;    int ptr=0;    int length=strlen(target);
 prefixed=(QP>=length);
 while (prefixed && ptr!=length) { prefixed=(Lower(QArr[ptr+1])==target[ptr]); ptr++; }
 return(prefixed);
}
```

<!-- PDF p.248 / printed p.xv -->

```c
/* ------------------------------------------------------------------------------------ */
int QArrMatchedWith(target)   char target[];
{
 int matched;    int ptr=0;
 matched=(QP==strlen(target));
 while (matched && ptr!=QP) { matched=(Lower(QArr[ptr+1])==target[ptr]); ptr++; }
 return(matched);
}
/* ------------------------------------------------------------------------------------ */
CopyQBuffSBuff()
{
 SP=0; while (SP!=QP) { SP++; SArr[SP]=QArr[SP]; }
}
/* ------------------------------------------------------------------------------------ */
CopyQBuffRpBuff()
{
 RpP=0; while (RpP!=QP) { RpP++; RpArr[RpP]=QArr[RpP]; }
}
/* ------------------------------------------------------------------------------------ */
CopyQBuffToString(string,ptr)   char *string;   int ptr;
{
 while (ptr!=QP) { *string=QArr[ptr+1]; string++; ptr++; }    *string='\0';
}
/* ------------------------------------------------------------------------------------ */
CopySBuffToString(string)   char *string;
{
 int ptr=0; while (ptr!=SP) { *string=SArr[ptr+1]; if (*string==nl) { *string='|'; }
                              string++; ptr++;
                            }
 *string='\0';
}
/* ------------------------------------------------------------------------------------ */
CopyRBuffToString(string)   char *string;
{
 int ptr=0; while (ptr!=RpP) { *string=RpArr[ptr+1]; if (*string==nl) { *string='|'; }
                               string++; ptr++;
                             }
 *string='\0';
}
/* ------------------------------------------------------------------------------------ */
int GetSBuffNL()
{
 int NumNL=0;   int SPptr=0;
 while (SPptr!=SP) { SPptr++; if (SArr[SPptr]==nl) NumNL++; }
 return(NumNL); }

/* ------------------------------------------------------------------------------------ */
int GetRpBuffNL()
{
 int NumNL=0;   int RpPptr=0;
 while (RpPptr!=RpP) { RpPptr++; if (RpArr[RpPptr]==nl) NumNL++; }
 return(NumNL); }

/* ------------------------------------------------------------------------------------ */




                                  /* IMPLEMENTATION OF DOC9 */ /* [?630] */
                                /* ========================== */
```

<!-- PDF p.249 / printed p.xvi -->

```c
#include <stdio.h>
#include "/se/daven/ox/c/c2/externglobals.c"

/* ---------------------------------------------------------------------------------- */
int OP_Doc9()
{
 int prevDocNL=DocNL;  int prevCP=CP;   int prevLP=LP;   int prevRP=RP;   int prevQP=QP;
 int prevCurY=CurY;    int first;       int last;        int temp;        int rep;
 if       (OP==NotImplemented)
            { return(OPNotImplemented); }
 else if (OP==CentreWindow)
            { return(CentreWindow_Doc9()); }
 else if (OP==RefreshDisplay)
            { return(RefreshDisplay_Doc9()); }
 else if (OP==CursorUpPage)
            { return(Screen_UpPage()); }
 else if (OP==CursorDownPage)
            { return(Screen_DownPage()); }
 else if (OP==Replace)
            { return(Screen_Replace(prevCurY)); }
 else if (OP==ShowDocStats)
            { return(Screen_ShowDocStats()); }
 else
            { if ((rep=OP_Doc8())!=OK)
                    { return(rep); }
              else
                    {  if (EState==State_Quote)
                            { if (prevQP!=QP) DisplayQuoteBuffer(); }
                       else
                            { CheckFlashBrackets();
                              first=prevCurY-WinOffY;
                              last=first+DocNL-prevDocNL+NLRem-NLIns;
                              if (first>last)     { temp=first; first=last; last=temp; }
                              WindowPolicy(first,last);
                            }
                       return(OK);
                    }
            }
}
/* ---------------------------------------------------------------------------------- */
int Initialize_Doc9()
{
 int ptr=0;   Initialize_Doc8();
 CLSAdjust(); PromptCur=WinWidth; PosImage(); WinOffX=0; WinOffY=0; SetDocCursor(); /* [?701] */
 while (ptr!=WinHeight) { WinLineOK[ptr+1]=FALSE; ptr++; } /* [?702] */
}
/* ---------------------------------------------------------------------------------- */
int CentreWindow_Doc9()
{
 if (EState==State_Doc) /* [?703] */
      { if      (CurY-WinOffY>=HalfWinHeight)
                     { OPType=RightMove; MoveWindowDown(CurY-WinOffY-HalfWinHeight);
                       SetDocCursor(); return(OK);
                     }
        else if (CurY-WinOffY<HalfWinHeight && CurY>=HalfWinHeight)
                     { OPType=LeftMove; MoveWindowUp(HalfWinHeight-CurY+WinOffY);
                       SetDocCursor(); return(OK);
                     }
        else
                     { return(TooNearTop); }
      }
 else
      { return(OP_Doc8()); }
```

<!-- PDF p.250 / printed p.xvii -->

```c
}
/* ---------------------------------------------------------------------------------- */
int RefreshDisplay_Doc9()
{
 CLSAdjust(); return(OK);
}
/* ---------------------------------------------------------------------------------- */
Screen_UpPage()
{
 int rep=OP_Doc8(). /* [?704] */
 if (rep==OK)
       {  if      (WinOffY>=PageHeight)              { MoveWindowUp(PageHeight); } /* [?705] */
          else if (WinOffY<PageHeight && WinOffY!=0) { MoveWindowUp(WinOffY); }
       }
 return(rep);
}
/* ---------------------------------------------------------------------------------- */
Screen_DownPage()
{
 int rep=OP_Doc8(); /* [?706] */
 if (rep==OK) { MoveWindowDown(PageHeight); }
 return(rep);
}
/* ---------------------------------------------------------------------------------- */
Screen_Replace(prevCurY)   int prevCurY;
{
 int SBuffNL;  int RpBuffNL;   int rep;
 if ((rep=OP_Doc8())==OK)
      { SBuffNL=GetSBuffNL(); RpBuffNL=GetRpBuffNL();
        if   (SBuffNL==RpBuffNL)
                { WindowLinesBad(prevCurY-WinOffY,prevCurY-WinOffY+SBuffNL); }
        else
                { WindowLinesBad(prevCurY-WinOffY,WinHeight); }
        if (SP<RpP) { OPType=RightMove; } else { OPType=LeftMove; }
        WindowPolicy();
      }
 return(rep);
}
/* ---------------------------------------------------------------------------------- */
int Screen_ShowDocStats()
{  int ptr=0;
 if (EState==State_Doc)    { PromptMessage(ShowState); PromptDisplayed=FALSE; return(OK); }
 else                      { return(OP_Doc8()); }
}
/* ---------------------------------------------------------------------------------- */
CheckFlashBrackets()
{
 int prevCP=CP;   int prevStartln=Startln;   char closebracket=OPChar;  int count=0;
 int NumNL=0;     int nomatch=TRUE;          char openbracket;          char arrchar;
 int x;           int y;
 if (OP==InsertChar &&
     (OPChar=='}' || OPChar==']' || OPChar==')' || OPChar=='>') &&
      Not(CharAvailable()))
      { if      (closebracket=='}')  { openbracket='{'; }
        else if (closebracket==']')  { openbracket='['; }
        else if (closebracket==')')  { openbracket='('; }
        else                         { openbracket='<'; } /* [?707] */
        while (CP>WinStartln+WinOffX+1 && nomatch)
              { CP--; arrchar=GetArrCont(CP);
                if      (arrchar==nl)
                             { NumNL++; }
                else if (arrchar==closebracket) /* [?708] */
                             { count++; }
                else if (arrchar==openbracket)
```

<!-- PDF p.251 / printed p.xviii -->

```c
                             { if (count>0)
                                     { count--; }
                               else
                                     { SetStartln(); x=CP-Startln+1-WinOffX;
                                       y=CurY-NumNL-WinOffY; nomatch=FALSE;
                                       if (x-1>=1 && x-1<=WinWidth &&
                                           y>=1 && y<=WinHeight)
                                             { WindowLinesBad(y+NumNL,y+NumNL);
                                               DisplayWindowRange(y+NumNL,y+NumNL);
                                               fflush(stdout);
                                               SetTermCursor(x-1,y); fflush(stdout);
                                               delay(); CP=prevCP; Startln=prevStartln;
                                             }
                                     }
                             }
              }
        CP=prevCP; Startln=prevStartln;
      }
}
/* ---------------------------------------------------------------------------------- */
SetWinStartln()
{
 register int numnl=CurY-WinOffY-1;
 WinStartln=Startln;  while (numnl!=0) { WinStartln=GetPrevStartln(WinStartln); numnl--; }
}
/* ---------------------------------------------------------------------------------- */
int GetPrevStartln(ptr)   register int ptr;
{
 ptr--;  while (ptr!=0 && GetArrCont(ptr)!=nl) { ptr--; }  return(ptr);
}
/* ---------------------------------------------------------------------------------- */
int GetNextStartln(ptr)   register int ptr; /* [?709] */
{
 if (ptr!=Max+LP-RP) { ptr++;
                       while (ptr!=Max+LP-RP && GetArrCont(ptr)!=nl) { ptr++; }
                     }
 return(ptr);
}
/* ---------------------------------------------------------------------------------- */
int DisplayWindowLine(startlnptr)   register int startlnptr; /* [?710] */
{
 register int x=0;
 while (startlnptr+x!=Max+LP-RP && GetArrCont(startlnptr+x+1)!=nl && x!=WinOffX)
          { x++; }
 while (startlnptr+x!=Max+LP-RP && GetArrCont(startlnptr+x+1)!=nl && x!=WinOffX+WinWidth)
          { putchar(GetArrCont(startlnptr+x+1)); x++; }
 if (x!=WinOffX+WinWidth) { ClearToEndOfLine(); }
}
/* ---------------------------------------------------------------------------------- */
DisplayWindowRange(first,last)   register int first;   register int last;
{
 register int ptr=WinStartln;   register int y=first;
  while (y!=1) { ptr=GetNextStartln(ptr); y--; }
  while (first<=last && Not(CharAvailable()) && NoInterrupt)
          { if (Not(WinLineOK[first]))
                  { SetTermCursor(1,first); DisplayWindowLine(ptr);
                    WinLineOK[first]=TRUE;
                  }
            ptr=GetNextStartln(ptr); first++;
          }
}
/* ---------------------------------------------------------------------------------- */
WindowLinesBad(first,last)   int first;   int last;
{
```

<!-- PDF p.252 / printed p.xix -->

```c
 if       (first<1)        { first=1; }
 else if (last>WinHeight) { last=WinHeight; }
 while (first<=last) { WinLineOK[first]=FALSE; first++; }
}
/* ---------------------------------------------------------------------------------- */
DisplayTheWindow()
{
 DisplayWindowRange(1,WinHeight);
}
/* ---------------------------------------------------------------------------------- */
DisplayCurLine()
{
 SetTermCursor(1,CurY-WinOffY); DisplayWindowLine(Startln);
}
/* ---------------------------------------------------------------------------------- */
MoveWindowDown(y,first)   int y:   int first; /* [?711] */
{
 WinOffY=WinOffY+y;  SetWinStartln(); /* [?712] */
 if (OPType==RightMove)
       { if    (y<=HalfWinHeight+1) { ScrollUpAdjust(y); } /* [?713] */
         else                       { WindowLinesBad(1,WinHeight); }
       }
 else
       { if (y+WinHeight-first<=HalfWinHeight+1) { WindowLinesBad(first,WinHeight); /* [?714] */
                                                    ScrollUpAdjust(y);
                                                  }
         else                                     { WindowLinesBad(1,WinHeight); }
       }
}
/* ---------------------------------------------------------------------------------- */
MoveWindowUp(y,last)   int y;   int last;
{
 WinOffY=WinOffY-y;  SetWinStartln();
 if (OPType==LeftMove) { if    (y<=HalfWinHeight+1) { ScrollDownAdjust(y,1); }
                         else                        { WindowLinesBad(1,WinHeight); }
                       }
 else                  { if (last<=HalfWinHeight+1)
                                { WindowLinesBad(1,last);
                                  if (last<=CurY-WinOffY) /* [?715] */
                                        { ScrollDownAdjust(CurY-WinOffY-last,last+1); }
                                  else
                                        { ScrollUpAdjust(last-CurY+WinOffY); }
                                }
                         else
                                { WindowLinesBad(1,WinHeight); }
                       }
}
/* ---------------------------------------------------------------------------------- */
MoveWindowLeft(x)   int x;
{
 WinOffX=WinOffX-x; WindowLinesBad(1,WinHeight);
}
/* ---------------------------------------------------------------------------------- */
MoveWindowRight(x)   int x;
{
 WinOffX=WinOffX+x; WindowLinesBad(1,WinHeight);
}
/* ---------------------------------------------------------------------------------- */
WindowPolicy(first,last)   int first;   int last;
{
 int winx=CurX-WinOffX;   int winy=CurY-WinOffY;
 if    (winx>=1 && winx<=WinWidth)
                 { if    (winy>=1 && winy<=WinHeight) { CursorInWindow(first,last); }
                   else                               { Scroll(first,last); }
```

<!-- PDF p.253 / printed p.xx -->

```c
                 }
 else
                 { if    (winy>=1 && winy<=WinHeight) { Pan(); }
                   else                               { ScrollAndPan(); }
                 }
}
/* ---------------------------------------------------------------------------------- */
Scroll(first,last)   int first;   int last;
{
 int winy=CurY-WinOffY;
 if       (winy<1 && CurY>=QtrWinHeight)
            { MoveWindowUp(WinOffY-CurY+QtrWinHeight,last); }
 else if (winy<1 && CurY<QtrWinHeight)
            { MoveWindowUp(WinOffY,last); }
 else
            { MoveWindowDown(CurY-PageHeight-WinOffY,first); }
}
/* ---------------------------------------------------------------------------------- */
Pan()
{
 int winx=CurX-WinOffX;
 if       (winx<1 && CurX>=QtrWinWidth) { MoveWindowLeft(WinOffX-CurX+QtrWinWidth), } /* [?716] */
 else if (winx<1 && CurX<QtrWinWidth)  { MoveWindowLeft(WinOffX); }
 else                                   { MoveWindowRight(CurX-PageWidth-WinOffX); }
}
/* ---------------------------------------------------------------------------------- */
ScrollAndPan()
{
 int winy=CurY-WinOffY;
 if       (winy<1 && CurY>=QtrWinHeight) { WinOffY=CurY-QtrWinHeight; }
 else if (winy<1 && CurY<QtrWinHeight)  { WinOffY=0; }
 else                                    { WinOffY=CurY-PageHeight; }
 SetWinStartln(); Pan();
}
/* ---------------------------------------------------------------------------------- */
CursorInWindow(first,last)   int first;   int last;
{
 if (OPType!=LeftMove && OPType!=RightMove && OPType!=NoMove)
       { if (first==last)
               { DisplayCurLine(); }
         else
               { if (last>HalfWinHeight || last>=DocNL+1-WinOffY) /* [?717] */
                       { WindowLinesBad(first,WinHeight);
                         DisplayWindowRange(first,WinHeight); } /* [?718] */
                 else
                       { if (OPType==LeftInsert || OPType==RightInsert)
                                    { WindowLinesBad(first,last);
                                      ScrollDownAdjust(last-first,last+1);
                                    }
                         else if (OPType==LeftDelete || OPType==RightDelete)
                                    { WindowLinesBad(1,last+last-first);
                                      ScrollUpAdjust(last-first);
                                    }
                       }
               }
       }
}
/* ---------------------------------------------------------------------------------- */
DisplayQuoteBuffer()
{
 register int ptr=0;   char c;
 SetInitQuoteCursor();
 while (ptr!=QP && ptr!=WinWidth-QuotePromptLength-1)
      { c=QArr[ptr+1];
```

<!-- PDF p.254 / printed p.xxi -->

```c
        if    (c==nl) { putchar('|'); } /* [?719] */
        else          { putchar(QArr[ptr+1]); }
        ptr++;
      }
 while (ptr!=WinWidth-QuotePromptLength-1) { putchar(sp); ptr++; } SetQuoteCursor();
}
/* ---------------------------------------------------------------------------------- */
```

[Remainder of page blank.]

<!-- PDF p.255 / printed p.xxii -->

# Appendix C

## Implementation Of The Editor Specification (Continued)

```c
                                    /* main.c */
                                  /* ======== */ /* [?720] */

#include <stdio.h>
#include <signal.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/ioctl.h>
#include <sys/fcntl.h>
#include "/se/daven/ox/c/c2/globals.c"
#include "/se/daven/ox/c/c1/read.c"
#include "/se/daven/ox/c/c1/write.c"
#include "/se/daven/ox/c/c2/screen.c"
#include "/se/daven/ox/c/c2/term.c"
#include "/se/daven/ox/c/c2/sysentryexit.c"
#include "/se/daven/ox/c/c2/messages.c"
#include "/se/daven/ox/c/c2/utilities.c"
/* ---------------------------------------------------------------------------------- */
main(args,argval)   int args;   char *argval[];

     /* "args" is the number of arguments present in system command line   */
     /* "argval" is the array of argument addresses in system command line */
{
 int InitialLine=1;   int cntrlfound=FALSE;   int newfile=FALSE;   int rep;
 Backup=FALSE; TerminalSet=FALSE; ScreenCleared=FALSE; Kbdptr=0; NoInterrupt=TRUE;
 GetTermCapAndSetWin(); ReadTermMode(); SetTerminal(); SysEntry(args,argval,&InitialLine);

GetNextChar(); /* [?721] */

 rep=(StartEditFile(FName,&cntrlfound,&newfile));
 if    (rep!=OK) { SysExit(rep,FName); }
 else            { OP=MoveToTop; OP_Doc8();
                   while (InitialLine!=1) { OP=RightMoveLine; OP_Doc8(); InitialLine--;} /* [?722] */
                   if (CurY>WinHeight) { WinOffY=CurY-PageHeight; SetWinStartln(); }
                   DisplayTheWindow();
                   if    (newfile)  { PromptMessage(EditingNewFile); PromptDisplayed=FALSE;}
                   else             { PromptMessage(EditingFile); PromptDisplayed=TRUE;}
                   if (cntrlfound) { PromptMessage(CntrlFound); }
                   SetDocCursor(); fflush(stdout);
                 }
 while (TRUE) { OPType=NoMove; ExecuteCommand();
                if (EState==State_Doc)
                      { if (Not(CharAvailable())) { DisplayTheWindow(); }
                        if (Not(NoInterrupt)) { PromptMessage(Interrupted);
                                                ClearInterrupt();
                                              }
                        SetDocCursor();
                      }
                else
                      { SetQuoteCursor(); }
                fflush(stdout);
              }
}
/* ---------------------------------------------------------------------------------- */
```

<!-- PDF p.256 / printed p.xxiii -->

```c
ExecuteCommand()
{
 int rep=OP_Doc9(KbdRead());
 if (EState==State_Doc)
       { if (rep==OK)
               { if (Not((PromptDisplayed)) && OP!=Quote && OP!=UpSearch &&
                     OP!=DownSearch && OP!=Replace && OP!=Input && OP!=Save && /* [?723] */
                     OP!=Write && OP!=ShowDocState)
                         { PromptMessage(EditingFile); }
               }
         else
               { PromptMessage(rep); }
         /* SetDocCursor(); */
       }
 else
       { if (rep!=OK) { RingBell(); } }
 /* fflush(stdout); */
}
/* ---------------------------------------------------------------------------------- */



                                    /* read.c */
                                  /* ======== */ /* [?724] */

/* ---------------------------------------------------------------------------------- */
int StartEditFile(filename,ctrlfound,newfile)   char *filename;   int *ctrlfound;
                                                int *newfile;
   /* "filename" is a pointer to a file, Checks to see if edit possible (if the file  */
   /* either doesn't exist and can be created, or if it exists then it must read      */ /* [?725] */
   /* permission and must not exceed the editor's capacity). Returns appropriate rep. */ /* [?726] */
   /* and sets *cntrlfound to TRUE if a control character read (which is discarded)   */
{
 int rep;  struct stat stbuf;
 if (FileExists(filename,&stbuf))
       { if (NotDirectory(&stbuf))
               { if (ReadPermission(filename))
                       { Initialize_Doc9(); OP=Input; OPType=LeftInsert;
                         rep=ReadFromStore(filename,&stbuf,ctrlfound);
                         Update_Doc3(0,0,Max); Update_Doc4(); Update_Doc6(0); /* [?727] */
                         return(rep);
               }
                 else
                       { SysExit(NoReadPermission); }
               }
         else
               { SysExit(Directory); }
       }
 else
       { if (WritePermission(filename))
               { Initialize_Doc9(); ScreenCleared=TRUE; *newfile=TRUE; return(OK); }
         else
               { SysExit(NoWritePermission); }
       }
}
/* ---------------------------------------------------------------------------------- */
int FileExists(filename,stbufptr)   char *filename;   struct stat *stbufptr;

  /* "filename" points to the file. "stbufptr" is a pointer to stbuf. A "stat" call */
```

<!-- PDF p.257 / printed p.xxiv -->

```c
  /* is attempted, and, if successful, TRUE returned, else FALSE returned.          */
{
 return((stat(filename,stbufptr)!=-1));
}
/* ---------------------------------------------------------------------------------- */
int NotDirectory(stbufptr)   struct stat *stbufptr;

  /* "filename" points to the file. "stbufptr" is a pointer to stbuf. If file not */
  /* a directory, function returns TRUE, else returns FALSE                       */
{
 return((stbufptr->st_mode & S_IFDIR) ^ S_IFDIR); /* [?728] */
}
/* ---------------------------------------------------------------------------------- */
ReadPermission(filename)   char *filename; /* [?729] */

      /* "filename" a pointer to a file. If file has read permission, function */
      /* returns TRUE, else returns FALSE                                       */
{
 FILE *fopen(),*SysPtr;
 SysPtr=fopen(filename,"r");
 if (SysPtr!=NullPtr) { fclose(SysPtr); return(TRUE); }
 else                 { return(FALSE); }
}
/* ---------------------------------------------------------------------------------- */
WritePermission(filename)   char *filename;

         /* "filename" is a pointer to a filename. If file can be written to */
         /* function returns TRUE, else returns FALSE                        */
{
 FILE *fopen(),*SysPtr;
 if ((SysPtr=fopen(filename,"w"))!=NullPtr      )            /* if file can be opened ... */ /* [?730] */
       { fclose(SysPtr); unlink(filename); return(TRUE); } /* ... close and delete it    */
 else                                                       /* else file can't be opened */
       { return(FALSE); }
}
/* ---------------------------------------------------------------------------------- */
int ReadFromStore(filename,stbufptr,ctrlfound)   char *filename:    struct stat *stbufptr; /* [?731] */
                                                 int *ctrlfound;

      /* If control characters found, discarded and *ctrlfound set to TRUE  */
      /* except for TAB controls, which are expanded in "ExpandTabs".       */
{
 int prevLP=LP;   int lineX=0;   int NoReadError=TRUE;    int cntrlfnd;   int x;
 FILE *fopen(),*SysPtr;          int filelength=FileLength(stbufptr);
 SetPromptMsg(filename);
 if    (filelength<=RP-LP)
         { if ((SysPtr=fopen(filename,"r"))!=NullPtr)
                 { ScreenCleared=TRUE; Standardize_Doc1(); PromptMessage(ReadingFile);
                   while (LP<RP && NoReadError && filelength>0 && NoInterrupt)
                           { x=getc(SysPtr); filelength--;
                             cntrlfnd=ControlChar(x);
                             while (cntrlfnd && filelength>0  && NoInterrupt)
                                     { *ctrlfound=TRUE; x=getc(SysPtr); filelength--;
                                       cntrlfnd=ControlChar(x);
                                     }
                             if (x==LF || x==RET) { x=nl; }
                             Arr[LP+1]=x; LP++; lineX++;
                             if      (x==nl)   { lineX=0; StripTrailWS(); }
                             else if (x==TAB)  { ExpandTabs(&lineX); }
                             NoReadError=(x!=EOF && NoInterrupt);
                           }
                   fclose(SysPtr);
                   if      (LP==RP)             { LP=prevLP; return(Full_Tabs); }
                   else if (Not(NoReadError)) { LP=prevLP; return(ReadError); }
```

<!-- PDF p.258 / printed p.xxv -->

```c
                   else                         { CP=LP; PromptMessage(Done); return(OK); }
                 }
           else
                 { return(CannotOpenFile); }
         }
 else
         { return(Full); }
}
/* ---------------------------------------------------------------------------------- */
int FileLength(stbufptr)   struct stat *stbufptr;

              /* "stbufptr" is a pointer to "stbuf" in StartEditFile */
{
 return(stbufptr->st_size);
}
/* ---------------------------------------------------------------------------------- */
int ControlChar(x)   int x;
{
 return((x<' ' || x>'~') && x!=RET && x!=TAB && x!=LF); /* [?732] */
}
/* ---------------------------------------------------------------------------------- */
ExpandTabs(ptrlineX)   int *ptrlineX;
{
 Arr[LP]=sp; (*ptrlineX)=tabstop-((*ptrlineX)%tabstop);
 if (*ptrlineX==8) { *ptrlineX=0; }
 while ((*ptrlineX)!=0 && LP<RP) { Arr[LP+1]=sp; LP++; (*ptrlineX)--; }
}
/* ---------------------------------------------------------------------------------- */
StripTrailWS()
{
 while(LP>CP+1 && Arr[LP-1]==sp) { LP--; Arr[LP]=nl; }
}
/* ---------------------------------------------------------------------------------- */




                                    /* write.c */
                                  /* ========= */ /* [?733] */

/* ---------------------------------------------------------------------------------- */
int WriteToStore(filename,filemode,first,last)   char filename[];   char filemode[];
                                                 int  first;        int  last;
{
 FILE *fopen(),*SysPtr;    int NoWriteError=TRUE;    int ptr=first-1;
 SysTranslate(filename); SysPtr=fopen(filename,filemode);
 SetPromptMsg(filename);
 if (SysPtr!=NullPtr)
      { PromptMessage(WritingFile);
        while (NoWriteError && ptr!=last)
                { NoWriteError=((putc(GetArrCont(ptr+1),SysPtr)!=EOF) && NoInterrupt);
                  ptr++;
                }
        if (NoWriteError && GetArrCont(ptr)!=nl)
              { NoWriteError=((putc(nl,SysPtr)!=EOF) && NoInterrupt); }
        fclose(SysPtr);
        if    (NoWriteError) { PromptMessage(Done); return(OK); }
        else                 { return(WriteError); }
      }
 else
```

<!-- PDF p.259 / printed p.xxvi -->

```c
      { return(CannotOpenFile); } /* [?734] */
}
/* ---------------------------------------------------------------------------------- */
void WriteBackupFile()

      /* FName++ (FName with "++" appended) is first unlinked, and, if possible, */
      /* FName++ is linked to FName. An appropriate PromptMessage is sent.        */
{
 char backupFName[FNameMaxx];
 strcpy(backupFName,FName); strcat(backupFName,"++");
 SetPromptMsg(backupFName); PromptMessage(UpdatingBackup); /* [?735] */
 unlink(backupFName);
 if (link(FName,backupFName)!=-1)                              /* new link can be made */
      { unlink(FName); }
 else                                                          /* new link can't be made */
      { PromptMessage(CannotUpdateBackup); }
}
/* ---------------------------------------------------------------------------------- */




                                    /* globals.c */
                                  /* =========== */ /* [?736] */

#include "consts.c"
/* ---------------------------------------------------------------------------------- */
int     LP,RP,CP;                                                     /* ConcDoc1 */
char    Arr[Maxx];

int     CurX,CurY,Startln,Endln,DocNL,WSRem,NLRem;                    /* ConcDoc3 */

int     WSIns,NLIns,PageWidth,PageHeight;                             /* ConcDoc4 */

int     MP,PP;                                                        /* ConcDoc6 */
char    PArr[Maxx];

char    QArr[QMaxx],SArr[QMaxx],RpArr[QMaxx];                         /* ConcDoc8 */
int     QP,QCP,SP,RpP;
int     MatchedLength;
char    FName[FNameMaxx];
int     FP;
int     EState;

int     WinOffX,WinOffY;                                              /* ConcDoc9 */
int     WinStartln;
int     WinLineOK[MaxWinHeight+2];
int     WinHeight,WinWidth;
int     HalfWinHeight,HalfWinWidth;
int     QtrWinHeight,QtrWinWidth;

char    KbdArr[kbdMaxx];                                              /* kbdread.c */ /* [?737] */
int     Kbdptr;
int     HomePath;
int     Key;
int     OP;
int     OPType; /* [?738] */
char    OPChar;
int     OPArr[kbdMaxx];
```

<!-- PDF p.260 / printed p.xxvii -->

```c
int     NoInterrupt;                                              /* sysentryexit.c */

int     Backup;                                                          /* write.c */

int     PromptDisplayed;                                       /* for prompt display */
int     DocChanged;
int     PromptCur;
char    PromptMsg[FNameMaxx];

short   ospeed;                                                           /* term.c */
int     TermType;
struct  sgttyb Sgttyb;
int     fcntlFlag;
int     TerminalSet;
int     ScreenCleared;

char    PC;                                       /* termcap padding character    */
char    CM[cntrlsize];                            /* termcap cursor motion        */
char    RC[cntrlsize];                            /* termcap carriage return      */
char    OD[cntrlsize];                            /* termcap down one line        */
char    SO[cntrlsize];                            /* termcap begin stand-out mode */ /* [?739] */
char    SE[cntrlsize];                            /* termcap end stand-out mode   */
char    CE[cntrlsize];                            /* termcap clear to end of line */
char    BL[cntrlsize];                            /* termcap ring bell            */
char    SR[cntrlsize];                            /* termcap reverse scroll       */
char    CL[cntrlsize];                            /* termcap clear entire screen  */
char    BC[cntrlsize];                            /* termcap backspace            */
char    UP[cntrlsize];                            /* termcap cursor up            */

/* ---------------------------------------------------------------------------------- */




                                    /* term.c */
                                  /* ========== */ /* [?740] */
/* ---------------------------------------------------------------------------------- */
GetTermCapAndSetWin()

   /* Loads "tcEntry" buffer from termcap. SysExit if terminal not defined or        */
   /* termcap not found, else termcap values initialized Sets WinWidth and WinHeight */
   /* using "ioctl" call, else termcap, else DefaultWinWidth and DefaultWinHeight;   */
   /* if larger than MaxWinWidth or MaxWinHeight, then SysExit.                      */
{
 struct ttysize ttysz;   char *ptr[cntrlsize];    char tcEntry[tcsize];
 char temp[cntrlsize];
 if ((TermType=getenv("TERM"))==0) { SysExit(NoTERM); }
 switch(tgetent(tcEntry,TermType)) { case  0 :  SysExit(UnknownTerminal); /* [?741] */
                                     case -1 :  SysExit(NoTermcapFile);
                                   }
 *ptr=CM; if (tgetstr("cm",ptr)==0) SysExit(InadeqTermCap,"cm");
 *ptr=RC; if (tgetstr("cr",ptr)==0) { RC[0]=CR; RC[1]=0; } /* [?742] */
 *ptr=OD; if (tgetstr("do",ptr)==0) { OD[0]=LF; OD[1]=0; }
 *ptr=SO; if (tgetstr("so",ptr)==0) if (tgetstr("md",ptr)==0) SysExit(InadeqTermCap,"so");
 *ptr=SE; if (tgetstr("se",ptr)==0) if (tgetstr("me",ptr)==0) SysExit(InadeqTermCap,"se"); /* [?743] */
 *ptr=CE; if (tgetstr("ce",ptr)==0) SysExit(InadeqTermCap,"ce");
 *ptr=BL; if (tgetstr("bl",ptr)==0) if (tgetstr("vb",ptr)==0) { BL[0]=BEL; BL[1]=0; }
 *ptr=SR; if (tgetstr("sr",ptr)==0) if (tgetstr("al",ptr)==0) SysExit(InadeqTermCap,"sr");
 *ptr=CL; if (tgetstr("cl",ptr)==0) SysExit(InadeqTermCap,"cl");
 *ptr=UP; if (tgetstr("up",ptr)==0) SysExit(InadeqTermCap,"up");
```

<!-- PDF p.261 / printed p.xxviii -->

```c
 BC[0]=BS;BC[1]=0;
 *ptr=BC; if (tgetflag("bs")==0) if (tgetstr("bc",ptr)==0) SysExit(InadeqTermCap,"bs");
 PC=PAD;
 *ptr=temp; if (tgetstr("pc",ptr)!=0) { PC=temp[0]; }
 if (ioctl(0,TIOCGSIZE,&ttysz)==-1 || ttysz.ts_lines<=0 || ttysz.ts_cols<=0)
      { ttysz.ts_cols=tgetnum("co");
        if (ttysz.ts_cols==-1)
              { SetSysCursor(); printf("Failed to get #columns of tty...setting default");
                ttysz.ts_cols=DefaultWinWidth; /* [?744] */
              }
        ttysz.ts_lines=tgetnum("li");
        if (ttysz.ts_lines==-1)
              { SetSysCursor(); printf("Failed to get #lines of tty...setting default");
                ttysz.ts_lines=DefaultWinHeight; /* [?745] */
              }
      }
 if (ttysz.ts_cols>MaxWinWidth)    { SysExit(TooManyColsTTY,ttysz.ts_cols); }
 if (ttysz.ts_lines>MaxWinHeight) { SysExit(TooManyRowsTTY,ttysz.ts_lines); }
 if (ttysz.ts_cols<=0) { SetSysCursor();
                         printf("Failed to get #columns in TTY ... setting default");
                       }
 WinWidth=ttysz.ts_cols;
 if (ttysz.ts_lines<=0) { SetSysCursor();
                          printf("Failed to get #lines in TTY ... setting default");
                        }
 WinHeight=ttysz.ts_lines;
 WinHeight--;                                                     /* for prompt line */
 if (WinHeight<MinWinHeight) { SysExit(WindowTooShort); } /* [?746] */
 if (WinWidth<MinWinWidth)   { SysExit(WindowTooNarrow); }
 SetOtherWinHeights();
 return;
}
/* ---------------------------------------------------------------------------------- */
SetOtherWinHeights()
{
 HalfWinHeight=(WinHeight/2); HalfWinWidth=(WinWidth/2);
 QtrWinHeight=(WinHeight/4); QtrWinWidth=(WinWidth/4);
 PageHeight=WinHeight-QtrWinHeight; PageWidth=WinWidth-QtrWinWidth; /* [?747] */
}
/* ---------------------------------------------------------------------------------- */
ReadTermMode()
{
 if    (ioctl(0,TIOCGETP,&Sgttyb)==0) { ospeed=Sgttyb.sg_ospeed; }
 else                                  { SysExit(SystemError,1,"ReadTermMode"); }
}
/* ---------------------------------------------------------------------------------- */
void SetfcntlFlags()
{
 if ((fcntlFlag=fcntl(0,F_GETFL))==-1) SysExit(SystemError,1,"SetfcntlFlags");
 if (fcntl(0,F_SETFL,fcntlFlag | FNDELAY)==-1) SysExit(SystemError,1,"SetfcntlFlags");
}
/* ---------------------------------------------------------------------------------- */
void ReSetfcntlFlags()
{
 if (fcntl(0,F_SETFL,fcntlFlag)==-1) SysExit(SystemError,1,"ReSetfcntlFlags");
}
/* ---------------------------------------------------------------------------------- */
void SetTerminal()
{
 struct sgttyb SgttybTemp;   int SgttybMask=~(RAW+CRMOD+ECHO+LCASE+CBREAK+TANDEM); /* [?748] */
 SgttybTemp=Sgttyb;
 SgttybTemp.sg_flags=((Sgttyb.sg_flags & SgttybMask) | (CBREAK+CRMOD) & (~XTABS)); /* [?749] */
 if (ioctl(0,TIOCSETP,&SgttybTemp)==-1) SysExit(SystemError,1,"SetTerminal");
 TerminalSet=TRUE;
```

<!-- PDF p.262 / printed p.xxix -->

```c
 SetfcntlFlags();
 if (strcmp(TermType,"vt220")==0)
       { printf("%c%c",ESC,'=');                                /* application keypad */
         printCSI(); printf("%c%d%c",'?',1,'h');           /* application cursor keys */
       }
}
/* ---------------------------------------------------------------------------------- */
ResetTerminal()
{
 if (ioctl(0,TIOCSETP,&Sgttyb)==-1) SysExit(SystemError,1,"ResetTerminal"); /* [?750] */
 ReSetfcntlFlags();
}
/* ---------------------------------------------------------------------------------- */




                                  /* sysentryexit.c */
                                /* ================ */ /* [?751] */

/* ---------------------------------------------------------------------------------- */
void SysEntry(args,argval,initline)   int  args;   char *argval[];   int *initline; /* [?752] */

    /* "args" is the number of arguments present, "argval" an array of addresses. */ /* [?753] */
    /* "initline" a pointer to InitialLine (from main). function checks syntax    */
    /* of input - if bad, SysExit, but if OK, FName, InitialLine, Backup and      */ /* [?754] */
    /* numfilenames set using SetNextOption - if numfilenames not 1, SysExit.     */
{
 int numfilenames=0;
 argval++; args--;
 while (args>0) { if (*argval[0]=='-')                           /* option specified ... */
                        { SetNextOption(&args,&argval,initline,&numfilenames); }
                  else                                              /*... else the filename */ /* [?755] */
                        { if (strlen(*argval)>=FNameMax-2) /* [?756] */
                               { SysExit(FilenameTooLong,*argval); }
                          strcpy(FName,*argval);
                          argval++; args--; numfilenames++;
                        }
                }
 if       (numfilenames==0) { SysExit(NoFilenameGiven); } /* [?757] */
 else if (numfilenames>1)  { SysExit(TooManyFilenames); }
 LoadFredcap(); SetInterrupts(); /* [?758] */
}
/* ---------------------------------------------------------------------------------- */
SetNextOption(as,av,i,f)   int  *as;   char **av[];
                           int  *i;    int    *f;

    /* "as" is a pointer to args, "av" points to the address of argval, "i" points to */
    /* InitialLine and "f" to numfilenames (all relating to SysEntry). The function   */ /* [?759] */
    /* takes the next argval, and, if recognized, (using the next argval if needed),  */
    /* sets the relevant flag. If the flag is not recognized, SysExit.                */ /* [?760] */

{
 if       (strcmp(**av,"-b")==0)                                /* backup flag recognized */
     { Backup=TRUE; (*av)++; (*as)--; }
 else if (strcmp(**av,"-l")==0)                           /* initial line flag recognized */ /* [?761] */
     { if (*as>1)                                             /* another argument to take */
         { (*av)++; (*as)--;
           if    (CnvStringToNum(**av,i)) { (*av)++; (*as)--; }   /* a valid line number */
           else                           { SysExit(BadLineNumber,**av); }
```

<!-- PDF p.263 / printed p.xxx -->

```c
         }
       else                                                     /* no line number present */
         { SysExit(BadCommandSyntax); }
     }
 else if (strcmp(**av,"-")==0)                              /* filename flag recognized */ /* [?762] */
     { if (*as>1)                                             /* another argument to take */
         { (*av)++; (*as)--;
           if (strlen(**av)>=FNameMax-2) { SysExit(FilenameTooLong,**av); }
           strcpy(FName,**av); (*av)++; (*as)--; (*f)++;
         }
      else
         { SysExit(NoFilenameGiven); }
     }
 else
     { SysExit(UnknownOption,**av); }
}
/* ---------------------------------------------------------------------------------- */
LoadFredcap()
{
 struct stat stbuf;   FILE *fopen(),*SysPtr;   int x;   int num;   int count;
 char filename[FNameMaxx];
 if ((HomePath=getenv("HOME"))==0) SysExit(NoHOMEset); /* [?763] */
 strcpy(filename,"~/fredcap/$TERM"); SysTranslate(filename);
 if (Not(FileExists(filename,&stbuf))) { strcpy(filename,DefaultFredPath);
                                         SysTranslate(filename);
                                       }
 if (Not(FileExists(filename,&stbuf)))      { SysExit(NoFredcapFile); }
 if ((SysPtr=fopen(filename,"r"))==NullPtr) { strcpy(FName,filename);
                                              SysExit(CannotOpenFredcap);
                                            }
 Key=0; while (Key!=kbdMax) { OPArr[Key]=NotImplemented; Key++; } /* [?764] */
 Key=0; x=getc(SysPtr);
 while (x!=EOF) { Key++;
                  while (x!=':' && x!=EOF) { x=getc(SysPtr); }
                  if (x!=EOF) { x=getc(SysPtr); /* [?765] */
                                if (x!=sp && x!=nl && x!=EOF)
                                      { num=0;
                                        while (IsDigitChar(x)) { num=(num*10)+(x-'0'); /* [?766] */
                                                                 x=getc(SysPtr);
                                                               }
                                        OPArr[Key]=num;
                                      }
                              }
                }
}
/* ---------------------------------------------------------------------------------- */
SysExit(rep,ptr,msg)   int rep;   int ptr;   char *msg;
{
 if (rep!=OK) { AbortMessage(rep,ptr); }
 SetSysCursor(); printf("\n");
 if (TerminalSet) { ResetTerminal(); }
 PosImage();
 if    (rep==SystemError) { perror(msg); printf("\n"); exit(stderr); }
 else                      { exit(rep); }
}
/* ---------------------------------------------------------------------------------- */
Interrupt()
{
 NoInterrupt=FALSE;
}
/* ---------------------------------------------------------------------------------- */
ClearInterrupt()
{
 NoInterrupt=TRUE;
```

<!-- PDF p.264 / printed p.xxxi -->

```c
}
/* ------------------------------------------------------------------------------------- */
Suspend()
{
 PosImage(); DisplayTheWindow(); SetSysCursor(); printf("\n");
 printf("%s Editing \"%s\"",EditorName,FName); fflush(stdout);
 if (TerminalSet) { ResetTerminal(); }
 sigsetmask(0); signal(SIGTSTP,SIG_DFL); kill(0,SIGTSTP);

 signal(SIGTSTP,Suspend); ClearInterrupt(); SetTerminal(); CLSAdjust(); DieplayTheWindow(); /* [?801] */
 if (EState==State_Doc)
        { PromptMessage(EditingFile); PromptMessage(Resumed); SetDocCursor(); }
 else
        { PromptMessage(ShowQuotePrompt); DisplayQuoteBuffer(); }
 fflush(stdout);
}
/* ------------------------------------------------------------------------------------- */
PanicExit()
{
 char filename[FNameMaxx];
 strcpy(filename,"~/fred.save"); SysTranslate(filename);
 if (DocChanged) { PanicWriteToStore(filename); }
 SetSysCursor(); printf("\n");
 if (TerminalSet) { ResetTerminal(); }
 PosImage();
 printf("Fatal interrupt received\n");
 if (DocChanged) { printf("Tried to save as \"%s\"\n",filename); }
 printf("\n"); exit(stderr);
}
/* ------------------------------------------------------------------------------------- */
int PanicWriteToStore(filename)   char *filename;
{
 int ptr=0;   FILE *fopen(),*SysFtr; SysPtr=fopen(filename,"w"); /* [?802] */
 if (SysPtr!=NullPtr)
       { while (ptr!=Max+LP-RP) { putc(GetArrCont(ptr+1),SysPtr); ptr++; }
         if (GetArrCont(ptr)!=nl) { putc(nl,SysPtr); }
         fclose(SysPtr);
       }
}
/* ------------------------------------------------------------------------------------- */
SetInterrupts()
{
 signal(SIGHUP,PanicExit);
 signal(SIGINT,Interrupt);
 signal(SIGQUIT,PanicExit);
 signal(SIGTSTP,Suspend);
}
/* ------------------------------------------------------------------------------------- */
SysTranslate(filename)   char *filename;
{
 int filelength=strlen(filename);   char newname[FNameMaxx];   int fptr=0;   int newptr=0;
 char var[FNameMaxx];   int val;
 while (fptr<filelength && newptr<FNameMax-2)
         { if       (filename[fptr]=='\\') { fptr++; newname[newptr]=filename[fptr];
                                              fptr++; newptr++;
                                            }
           else if (filename[fptr]=='~')  { fptr++;
                                              newptr=Insert(HomePath,uewname,newptr); /* [?803] */
                                            }
           else if (filename[fptr]=='$')  { fptr++;
                                              fptr=StripEnvVar(var,filename,fptr);
                                              if ((val=getenv(var))!=0)
                                                    { newptr=Insert(val,newname,newptr); }
                                            }
```

<!-- PDF p.265 / printed p.xxxii -->

```c
           else                             { newname[newptr]=filename[fptr];
                                              fptr++; newptr++;
                                            }
         }
 newname[newptr]='\0'; strcpy(filename,newname);
}
/* ------------------------------------------------------------------------------------- */
Insert(word,newname,newptr)   char *word;   char *newname;   int newptr;
{
 int wordlength=strlen(word);   int ptr=0;
 while(ptr<wordlength && newptr<FNameMar-2) { newname[newptr]=word[ptr]; ptr++; newptr++; } /* [?804] */
 return(newptr);
}
/* ------------------------------------------------------------------------------------- */
StripEnvVar(var,filename,fptr)   char *var;   char *filename;   int fptr;
{
 int ptr=0;   char c=filename[fptr];
 while (IsAlphaNum(c)) { var[ptr]=c; fptr++; ptr++; c=filename[fptr]; }
 var[ptr]='\0';  return(fptr);
}
/* ------------------------------------------------------------------------------------- */




                                /* screen.c */
                              /* ============ */
/* ------------------------------------------------------------------------------------- */
DisplayChar(c)   int c;
{
/* if (c==sp) { c='_'; } else if (c==nl) { c='|'; } */
 putchar(c);
}
/* ------------------------------------------------------------------------------------- */
ScreenOutput(cntrlstr,lines)   register char *cntrlstr;   int lines;
{ tputs(cntrlstr,lines,DisplayChar); }
/* ------------------------------------------------------------------------------------- */
CLSAdjust()
{ ScreenOutput(CL,WinHeight+1); WindowLinesBad(1,WinHeight);
  PromptCur=WinWidth; PromptDisplayed=FALSE;      }
/* ------------------------------------------------------------------------------------- */
SetTermCursor(x,y)   int x;   int y;
{

 if (strcmp(tgoto(CM,x-1,y-1),"OOPS")==0) { SysExit(SystemError,1,"OOPS"); } /* [?805] */

ScreenOutput(tgoto(CM,x-1,y-1),1); }
/* ------------------------------------------------------------------------------------- */
SetDocCursor()
{ SetTermCursor(CurX-WinOffX,CurY-WinOffY); }
/* ------------------------------------------------------------------------------------- */
SetPromptCursor()
{ SetTermCursor(PromptCur,WinHeight+1); }
/* ------------------------------------------------------------------------------------- */
SetInitQuoteCursor()
{ SetTermCursor(QuotePromptLength+1,WinHeight+1); }
/* ------------------------------------------------------------------------------------- */
SetQuoteCursor()
{ SetTermCursor(QCP+QuotePromptLength+1,WinHeight+1); }
/* ------------------------------------------------------------------------------------- */
```

<!-- PDF p.266 / printed p.xxxiii -->

```c
SetSysCursor()
{ if (ScreenCleared) { SetTermCursor(1,WinHeight+1); } printf("\n"); }
/* ------------------------------------------------------------------------------------- */
ScrollUpAdjust(n)   register int n;
{
 register int y=n;
 if (n!=0) { ErasePromptLine(); ScreenOutput(tgoto(CM,0,WinHeight),1);
             while (y!=0) { ScreenOutput(DO,WinHeight+1+y-n); y--; } /* [?806] */
             while (y+n<WinHeight) { WinLineOK[y+1]=WinLineOK[y+n+1]; y++; }
             PromptCur=WinWidth; PromptDisplayed=FALSE;
             ReDisplayPromptLine(); WindowLinesBad(WinHeight-n+1,WinHeight);
           }
}
/* ------------------------------------------------------------------------------------- */
ScrollDownAdjust(n,line)   register int n;   register int line;
{
 register int y=n;
 if (n!=0) { ScreenOutput(tgoto(CM,0,line-1),1);
             while (y!=0) { ScreenOutput(SR,WinHeight-line+1+y-n); y--; }
             while (y+line+n<=WinHeigbt) /* [?807] */
                     { WinLineOK[WinHeight-y]=WinLineOK[WinHeight-y-n]; y++; }
             PromptCur=WinWidth; PromptDisplayed=FALSE;
             ReDisplayPromptLine(); WindowLinesBad(line,line+n-1);
           }
}
/* ------------------------------------------------------------------------------------- */
ReDisplayPromptLine()
{
 char schstring[FNameMax];   char rplstring[FNameMax];
 if (Not(CharAvailable()))
       { PromptCur=WinWidth;
         if (EState==State_Doc)
                   { if       (OP==UpSearch)
                                 { PromptMessage(SearchingUpFor); PromptMessage(Found); }
                     else if (OP==DownSearch)
                                 { PromptMessage(SearchingDownFor); PromptMessage(Found);}
                     else if (OP==Replace)
                                 { CopySBuffToString(schstring);
                                   SetPromptMsg(schstring); PromptMessage(Replaced);
                                   CopyRBuffToString(rplstring);
                                   SetPromptMsg(rplstring); PromptMessage(With);
                                 }
                     else if (OP==Input)
                                 { PromptMessage(ReadingFile); PromptMessage(Done); }
                     else
                                 { PromptMessage(EditingFile); }
                   }
        else
                   { PromptMessage(ShowQuotePrompt); DisplayQuoteBuffer();
                     SetQuoteCursor();
                   }
       }
}
/* ------------------------------------------------------------------------------------- */
NegImage()
{ ScreenOutput(SO,1); }
/* ------------------------------------------------------------------------------------- */
PosImage()
{ ScreenOutput(SE,1); }
/* ------------------------------------------------------------------------------------- */
ClearToEndOfLine()
{ ScreenOutput(CE,1); }
/* ------------------------------------------------------------------------------------- */
RingBell()
```

<!-- PDF p.267 / printed p.xxxiv -->

```c
{ ScreenOutput(BL,1); }
/* ------------------------------------------------------------------------------------- */
ErasePromptLine()
{ int i=0;            PosImage(); PromptCur=1; SetPromptCursor();
                      while(i++!=WinWidth-1) { printf("%c",' '); }    }
/* ------------------------------------------------------------------------------------- */
DrawBlankPromptLine()
{ int i=0;            NegImage(); SetPromptCursor();
                      while(i++!=WinWidth-1) { printf("%c",' '); } PosImage();    }
/* ------------------------------------------------------------------------------------- */
CursorToNextLine()
{ ScreenOutput(DO,1); } /* [?808] */
/* ------------------------------------------------------------------------------------- */
printCSI()                                                /* print CSI sequence for vt220 */
{ printf("%c%c",ESC,'['); } /* [?809] */
/* ------------------------------------------------------------------------------------- */




                                /* externglobals.c */
                              /* ================== */

#include "consts.c"
/* -------------------------------------------------------------------------------------  */
extern int     LP,RP,CP;
extern char    Arr[Maxx];

extern int     CurX,CurY,Startln,Endln,DocNL,WSRem,NLRem; /* [?810] */

extern int     WSIns,NLIns,PageWidth,PageHeight;

extern int     MP,PP; /* [?811] */
extern char    PArr[Maxx];

extern char    QArr[QMaxx],SArr[QMaxx],RpArr[QMaxx];
extern int     QP,QCP,SP,RpP;
extern int     MatchedLength;
extern char    FName[FNameMaxx];
extern int     FP;
extern int     EState;

extern int     WinOffX,WinOffY;
extern int     WinStartln;
extern int     WinLineOK[MaxWinHeight+2];
extern int     WinHeight,WinWidth;
extern int     HalfWinHeight,HalfWinWidth;
extern int     QtrWinHetght,QtrWinWidth; /* [?812] */

extern char    KhdArr[kbdMaxx]; /* [?813] */
extern int     Kbdptr;
extern int     HomePath;
extern int     Key;
extern int     OP;
extern int     OPType;
extern char    OPChar;
extern int     OPArr[100];

extern int     NoInterrupt;
```

<!-- PDF p.268 / printed p.xxxv -->

```c
extern int     Backup;

extern int     PromptDisplayed;
extern int     DocChanged;
extern int     PromptCur;
extern char    PromptMsg[FNameMaxx];

extern short   ospeed;
extern int     TermType;
extern struct sgttyh Sgttyb; /* [?814] */
extern int     fcntlFlag;
extern int     TerminalSet;
extern int     ScreenCleared;

extern char    PC;
extern char    CM[cntrlsize];
extern char    RC[cntrlsize];
extern char    DO[cntrlsize]; /* [?815] */
extern char    SO[cntrlsize];
extern char    SE[cntrlsize];
extern char    CE[cntrlsize];
extern char    BL[cntrlsize];
extern char    SR[cntrlsize];
extern char    CL[cntrlsize];
extern char    BC[cntrlsize];
extern char    UP[cntrlsize];

/* ------------------------------------------------------------------------------------- */
```

```c
                                /* kbdinterpret.c */
                              /* ================= */

#include "externglobals.c"

/* ------------------------------------------------------------------------------------- */
KbdRead()
{
 if      (strcmp(TermType,"vt220")==0) { vt220Interpret(); }
 else if (strcmp(TermType,"sun")==0)   { SunInterpret(); }
}
/* ------------------------------------------------------------------------------------- */
vt220Interpret()                                      /* keyboard interpret for vt220 */
{
 char x=GetNextChar();
 if      (x>=' ' && x<='~')  { OP=InsertChar; OPChar=x; } /* [?816] */
 else if (x==RET)            { OP=InsertChar; OPChar=nl; }
 else if (x==TAB)            { OP=InsertChar; OPChar=x; }
 else if (x==DEL)            { OP=LeftDeleteChar; }
 else if (x==ESC)            { x=GetNextChar();
                               if      (x=='[') { vt220InterpretCSI(); }
                               else if (x=='O') { vt220InterpretSS3(); } /* [?817] */
                               else             { OP=NotImplemented; }
                             }
 else                        { OP=NotImplemented; }
}
/* ------------------------------------------------------------------------------------- */
vt220InterpretCSI()                                   /* function and editing keys */
```

<!-- PDF p.269 / printed p.xxxvi -->

```c
{
 char c;   char d;   char e;   int  i;   int j;
 c=GetNextChar(); d=GetNextChar();
 if (d=='~')                                                          /* editing keys */ /* [?818] */
     switch (c)
      {
       case '1' : break;                                              /* Find        */
       case '2' : OP=Mark; break;                                     /* Insert Here */
       case '3' : break;                                              /* Remove      */
       case '4' : break;                                              /* Select      */
       case '5' : break;                                              /* Prev Screen */
       case '6' : break;                                              /* Next Screen */
      }
 else {
       e=GetNextChar();
       if (e=='~')                                                   /* function keys */
           {
             i=(10*(c-'0'))+d-'0';
            switch(i)
             {
              case 17 : break;                                             /* F6   */
              case 18 : OP=CursorUpPage; break;                            /* F7   */
              case 19 : OP=MoveToTop; break;                               /* F8   */
              case 20 : OP=MoveToBot; break;                               /* F9   */
              case 21 : OP=CursorDownPage; break;                          /* F10  */

              case 23 : break;                                             /* F11  */
              case 24 : break;                                             /* F12  */
              case 25 : break;                                             /* F13  */
              case 26 : break;                                             /* F14  */

              case 28 : break;                                             /* Help */
              case 29 : break;                                             /* Do   */

              case 31 : OP=Cut; break;                                     /* F17  */
              case 32 : OP=Lift; break;                                    /* F18  */
              case 33 : OP=Paste; break;                                   /* F19  */
              case 34 : OP=NotImplemented; break;                          /* F20  */
             }
           }
       else  OP=NotImplemented;
      }
}
/* ------------------------------------------------------------------------------------- */
vt220InterpretSS3()                          /* arrow keys and auxiliary keypad */
{
 switch (GetNextChar())
  {
   case 'A' : OP=CursorUpLine; break;                                 /* up arrow    */
   case 'B' : OP=CursorDownLine; break;                               /* down arrow  */
   case 'C' : OP=CursorRightChar; break;                              /* right arrow */
   case 'D' : OP=CursorLeftChar; break;                               /* left arrow  */

   case 'P' : OP=LeftMoveLine; break;                                       /* PF1 */
   case 'Q' : OP=RightMoveLine; break;                                      /* PF2 */
   case 'R' : OP=LeftDeleteLine; break;                                     /* PF3 */
   case 'S' : OP=RightDeleteLine; break;                                    /* PF4 */

   case 'p' : break;                                                          /* 0 */
   case 'q' : break;                                                          /* 1 */
   case 'r' : break;                                                          /* 2 */
   case 'e' : break;                                                          /* 3 */ /* [?819] */
   case 't' : OP=LeftMoveChar; break;                                         /* 4 */
   case 'u' : OP=RightMoveChar; break;                                        /* 5 */
```

<!-- PDF p.270 / printed p.xxxvii -->

```c
   case 'v' : OP=LeftDeleteChar; break;                                       /* 6 */
   case 'w' : OP=LeftMoveWord; break;                                         /* 7 */
   case 'x' : OP=RightMoveWord; break;                                        /* 8 */
   case 'y' : OP=LeftDeleteWord; break;                                       /* 9 */

   case 'l' : OP=RightDeleteChar; break;                                /*  ,  */
   case 'm' : OP=RightDeleteWord; break;                                /*  -  */
   case 'n' : break;                                                    /*  .  */
   case 'M' : break;                                                    /* Enter */
  }
 }
/* ------------------------------------------------------------------------------------- */
SunInterpret()                                              /* keyboard read for sun */
{
 char x=GetNextChar();
 if      (x>=' ' && x<='~')  { OP=InsertChar; OPChar=x; }
 else if (x==RET)            { OP=InsertChar; OPChar=nl; }
 else if (x==TAB)            { OP=InsertChar; OPChar=x; }
 else if (x==DEL)            { OP=LeftDeleteChar; }
 else if (x==BS)             { OP=LeftMoveChar; }
 else if (x==ESC)            { x=GetNextChar();
                               if      (x=='[') { SunFunctionInterpret(); }
                               else             { OP=NotImplemented; }
                             }
 else                        { OP=NotImplemented; }
}
/* ------------------------------------------------------------------------------------- */
SunFunctionInterpret()
{
 char c=GetNextChar();   char d=GetNextChar();   char e=GetNextChar();
 char f=GetNextChar();   Key=0;
 if (f=='z') { switch((100*(c-'0'))+(10*(d-'0'))+(e-'0')) {
      case 192 : Key=L1; break;      case 234 : Key=L2; break;      case 203 : Key=L3; break;
      case 235 : Key=L4; break;      case 204 : Key=L5; break;      case 236 : Key=L6; break;
      case 205 : Key=L7; break;      case 237 : Key=L8; break;      case 206 : Key=L9; break; /* [?820] */
      case 238 : Key=L10; break;     case 202 : Key=F1; break;      case 225 : Key=F2; break;
      case 226 : Key=F3; break;      case 227 : Key=F4; break;      case 228 : Key=F5; break;
      case 229 : Key=F6; break;      case 230 : Key=F7; break;      case 231 : Key=F8; break;
      case 232 : Key=F9; break;      case 208 : Key=R1; break;      case 209 : Key=R2; break;
      case 210 : Key=R3; break;      case 211 : Key=R4; break;      case 212 : Key=R5; break;
      case 213 : Key=R6; break;      case 214 : Key=R7; break;      case 215 : Key=R8; break;
      case 216 : Key=R9; break;      case 217 : Key=R10; break;     case 218 : Key=R11; break;
      case 219 : Key=R12; break;     case 220 : Key=R13; break;     case 221 : Key=R14; break;
      case 222 : Key=R15; break; } }
 OP=OPArr[Key];
}
/* ------------------------------------------------------------------------------------- */




                                /* utilities.c */
                              /* =============== */

/* ------------------------------------------------------------------------------------- */
char GetNextChar()                                /* unbuffered single character input, */
{                                                 /* returns next key from keyboard     */
  char c=EOF;   int ptr=0;
  if    (Kbdptr!=0) { c=KbdArr[1]; Kbdptr--;
                      while (ptr!=Kbdptr) { KbdArr[ptr+1]=KbdArr[ptr+2]; ptr++; }
```

<!-- PDF p.271 / printed p.xxxviii -->

```c
                    }
  else              { while (c==EOF) read(0,&c,1); }
 return(c);
}
/* ------------------------------------------------------------------------------------- */
int CharAvailable()
{
 char c=EOF;
 read(0,&c,1); if  (c!=EOF && Kbdptr!=kbdMax) { Kbdptr++; KbdArr[Kbdptr]=c; } /* [?821] */
 return(Kbdptr!=0);
}
/* ------------------------------------------------------------------------------------- */
delay()
{
 int i=1000; while (i>0) { if (CharAvailable()) i=0; else i--; }
}
/* ------------------------------------------------------------------------------------- */
int Not(i)                                /* if "i" FALSE, returns TRUE else returns FALSE */
 int i;
{ if   (i==FALSE) return(TRUE);  else return(FALSE); }
/* ------------------------------------------------------------------------------------- */
int CnvStringToNum(string,ptr)/* "string" is a string, "ptr" a pointer to the value to  */
                              /* be assigned. if each member of the string is an        */
                              /* integer character, the value is assigned and TRUE      */
                              /* returned, else value left unchanged, and FALSE returned */
 char string[]; int  *ptr;
{
 int j=0;

 while (*string!=0 && IsDigitChar(*string)) { j=(10*j)+(*string-'0'); string++; }
 if (*string==0 && j!=0)                       /* end of string reached, so OK if not zero */
       { *ptr=j; return(TRUE); }
 else                                                      /* a non-digit character present */
       { return(FALSE); }
}
/* ------------------------------------------------------------------------------------- */
int CnvNumToString(num,string)   int num;   char *string;
{
 int ptr=0;   char tmpstring[FNameMaxx];
 while (num!=0 && ptr<FNameMax-2) { tmpstring[ptr]=('0'+(num%10));  ptr++; num=num/10; }
 while (ptr!=0) { ptr--; *string=tmpstring[ptr]; string++; }  *string='\0';
}
/* ------------------------------------------------------------------------------------- */
int IsDigitChar(c)                     /* returns TRUE if '0'<=c<='9', else returns FALSE */
 char c;
{ return('0'<=c && c<='9'); }
/* ------------------------------------------------------------------------------------- */
int IsAlphaNum(c)                  /* returns TRUE if c alpha-numeric, else returns FALSE */
 char c;
{ return(('a'<=c && c<='z') || ('A'<=c && c<='Z') && ('0'<=c || c<='9')); } /* [?822] */
/* ------------------------------------------------------------------------------------- */
int Lower(c)                                              /* converts ASCII to lower case */
 char c;
{
 if   (c>='A' && c<='Z') return(c+'a'-'A');
 else                    return(c);
}
/* ------------------------------------------------------------------------------------- */
```

<!-- PDF p.272 / printed p.xxxix -->

```c
                                /* consts.c */
                              /* ============= */

/* ------------------------------------------------------------------------------------- */
#define Maxx                  100001
#define Max                   Maxx-1                  /* array[0] not used! */ /* [?823] */
#define QMaxx                     65
#define QMax                 QMaxx-1
#define FNameMaxx                257
#define FNameMax         FNameMaxx-1
#define kbdMaxx                  101
#define kbdMax             kbdMaxx-1
#define tabstop                    8

#define MaxWinWidth              150                                   /* window lengths */
#define MaxWinHeight              60
#define MinWinWidth                8
#define MinWinHeight               8
#define DefaultWinWidth           80
#define DefaultWinHeight          24

#define cntrlsize                 32                                      /* for termcap */
#define tcsize                  1024

#define NUL                  '\000'                                /* special characters */
#define PAD                  '\000'
#define BEL                  '\007'
#define BS                   '\010'
#define TAB                  '\011'
#define RET                  '\012'
#define LF                   '\012'
#define CR                   '\015'
#define ESC                  '\033'
#define DEL                  '\177'
#define NullPtr                 NULL

#define sp                     ' '
#define nl                    '\n'

#define Left                       1                                     /* for ConcDoc1 */
#define Right                      2

#define CurAbove                   1                                     /* for ConcDoc6 */
#define CurBelow                   2

#define State_Doc                  0                        /* for ConcDoc8 */ /* [?824] */
#define State_Quote                1

#define TRUE                       1                                         /* booleans */
#define FALSE                      0

#define OK                         0                                  /* report messages */
#define SystemError                2
#define NoTERM                     3
#define UnknownTerminal            4
#define NoTermcapFile              5
#define InadeqTermCap              6
#define TooManyColsTTY             7
#define TooManyRowsTTY             8
#define WindowTooShort             9
#define WindowTooNarrow           10
#define ReadError                 11
#define WriteError                12
#define NoReadPermission          13
```

<!-- PDF p.273 / printed p.xl -->

```c
#define CannotOpenFile            14
#define BadTerminalType           15
#define NoFilenameGiven           16
#define BadLineNumber             17                                           /* [?825] */
#define TooManyFilenames          18
#define BadCommandSyntax          19
#define NoWritePermission         20
#define UnknownOption             21
#define Full                      22
#define Top                       23
#define Bot                       24
#define TopLine                   25
#define LeftEdge                  26
#define NoTextMarked              27                                           /* [?826] */
#define PBuffEmpty                28
#define TooNearTop                29
#define OPNotImplemented          30
#define QuoteError                31
#define TopQuote                  32
#define BotQuote                  33
#define FullQuote                 34
#define IllegalEditOp             35
#define IllegalQuoteChar          36
#define BellRung                  37
#define DocNotChanged             38
#define ReadingFile               39
#define WritingFile               40
#define EditingFile               41
#define EditingNewFile            42
#define Done                      43
#define UpdatingBackup            44
#define CannotUpdateBackup        45
#define Suspended                 46
#define ShowQuotePrompt           47
#define EditAborted               48                                           /* [?827] */
#define CntrlFound                50
#define Full_Tabs                 51
#define FileNotExist              52
#define Directory                 53
#define HitKeyToResume            54
#define NoCommandGiven            55
#define SearchingUpFor            56
#define SearchingDownFor          57
#define Found                     58
#define NotFound                  59
#define SBuffEmpty                60
#define Replaced                  61
#define With                      62
#define NotMatched                63
#define ShowStats                 64
#define DBuffEmpty                65
#define NoFredcapFile             66
#define CannotOpenFredcap         67
#define Resumed                   68
#define Interrupted               69
#define NoHOMEset                 70
#define FilenameTooLong           71

#define NotImplemented             0
#define MoveToTop                  1                                  /* editor commands */
#define MoveToBot                  2
#define LeftMoveChar               3
#define RightMoveChar              4
#define LeftMoveWord               5
```


<!-- PDF p.274 / printed p.xli -->

```c
#define RightMoveWord              6
#define LeftMoveLine               7
#define RightMoveLine              8
#define LeftDeleteChar             9
#define RightDeleteChar           10
#define LeftDeleteWord            11
#define RightDeleteWord           12
#define LeftDeleteLine            13
#define RightDeleteLine           14
#define CursorLeftChar            15
#define CursorRightChar           16
#define CursorUpLine              17
#define CursorDownLine            18
#define CursorUpPage              19
#define CursorDownPage            20
#define UpSearch                  21
#define DownSearch                22
#define Replace                   23
#define Mark                      24
#define Cut                       25
#define Lift                      26
#define Paste                     27
#define Quote                     28
#define CentreWindow              29
#define RefreshDisplay            30
#define ShowDocStats              31
#define Abort                     32
#define Save                      33
#define Write                     34
#define Append                    35
#define Quit                      36
#define Input                     37
#define MoveLineNumberOrError 38
#define Escape                    49                                           /* [?828] */
#define InsertChar                40

#define LeftInsert                 1                                       /* for OPType */
#define RightInsert                2
#define LeftDelete                 3
#define RightDelete                4
#define LeftMove                   5
#define RightMove                  6
#define NoMove                     7

#define L1                         1                                /* sun function keys */
#define L2                         2
#define L3                         3
#define L4                         4
#define L5                         5
#define L6                         6
#define L7                         7
#define L8                         8
#define L9                         9
#define L10                       10
#define F1                        11
#define F2                        12
#define F3                        13
#define F4                        14
#define F5                        15
#define F6                        16
#define F7                        17
#define F8                        18
#define F9                        19
#define R1                        20
```

<!-- PDF p.275 / printed p.xlii -->

```c
#define R2                        21
#define R3                        22
#define R4                        23
#define R5                        24
#define R6                        25
#define R7                        26
#define R8                        27
#define R9                        28
#define R10                       29
#define R11                       30
#define R12                       31
#define R13                       32
#define R14                       33
#define R15                       34


#define DefaultTermPath                      "/etc/termcap"
#define DefaultFredPath                           "~/$TERM"
#define EditorName                               "fred 0.0"

#define QuotePrompt                              "QUOTE : "
#define QuotePromptLength                                 8
#define usage "usage: fred [-b] [-l number] [-] filename" /* [?829] */
/* ------------------------------------------------------------------------------------- */




                                /* messages.c */
                              /* =============== */

/* ------------------------------------------------------------------------------------- */
AbortMessage(rep,ptr)   int rep;   int ptr;
{
 switch(rep)
  {
   case  UnknownTerminal    : printf("\nUnknown terminal type \"%s\"",TermType); break;
   case  NoTermcapFile      : printf("\nCan't find termcap file"); break;
   case  NoHOMEset          : printf("\nEnvironment variable HOME not found"); break;
   case  InadeqTermCap      : printf("\nInadequate terminal capabilities - %s",TermType);
                              printf(" / %s",ptr); break;
   case  TooManyColsTTY     : printf("\nToo many columns in TTY ... columns=%d",ptr);
                              printf(" max columns=%d",MaxWinWidth); break;
   case  TooManyRowsTTY     : printf("\nToo many rows in TTY ... rows=%d",ptr);
                              printf(" max rows=%d",MaxWinHeight); break;
   case  WindowTooShort     : printf("\nWindow too small ... lines=%d",WinHeight);
                              printf(" min lines=%d",MinWinHeight); break;
   case  WindowTooNarrow    : printf("\nWindow too small ... cols=%d",WinWidth);
                              printf(" min cols=%d",MinWinWidth); break;
   case  Full               : printf("\n\"%s\" too big for editor",FName);
                              printf("\n%s capacity:%d",EditorName,Max); break;
   case  Full_Tabs          : printf(" too big for editor \(tabs expanded\)");
                              PosImage(); printf("\n\n%s capacity:%d",EditorName,Max);
                              break;
   case  Directory          : printf("\n\"%s\" is a directory",FName); break;
   case  NoReadPermission   : printf("\nRead permission denied for \"%s\"",FName); break;
   case  CannotOpenFile     : printf("\nCannot open \"%s\"",FName); break;
   case  BadTerminalType    : printf("\nfred: not available for ");
                              printf("terminal type \"%s\"",FName); break;
   case  FilenameTooLong    : printf("\nFilename \"%s\" too long",ptr); break;
```

<!-- PDF p.276 / printed p.xliii -->

```c
   case  NoFilenameGiven    : printf("\nfred: no filename given ... "); printf(usage); break;
   case  BadLineNumber      : printf("\nfred: bad line number \"%s\"... ",ptr);
                              printf(usage); break;
   case  TooManyFilenames   : printf("\nfred: too many filenames ... "); printf(usage);
                              break;
   case  BadCommandSyntax   : printf("\nfred: bad syntax ... "); printf(usage); break;
   case  NoWritePermission  : printf("\nWrite permission denied for file \"%s\"",FName);
                              break;
   case  UnknownOption      : printf("\nfred: Unknown option %s ... ",ptr);
                              printf(usage); break;
   case  NoFredcapFile      : printf("\nCan't find fredcap file"); break;
   case  CannotOpenFredcap  : printf("\nCan't open fredcap file \"%s\"",FName); break;
  }
}
/* ------------------------------------------------------------------------------------- */
PromptMessage(rep)   int rep;
{
 NegImage(); switch(rep)
 {
   case  Top :
            Prompt(1,"At top of document"); MsgEnd(); break;
   case  Bot :
            Prompt(1,"At bottom of document"); MsgEnd(); break;
   case  Full :
            Prompt(1,"Editor capacity reached"); MsgEnd(); break;
   case  Full_Tabs :
            Prompt(0,"Editor capacity exceeded expanding tabs"); MsgEnd(); break;
   case  TopLine :
            Prompt(1,"At top line of document"); MsgEnd(); break;
   case  LeftEdge :
            Prompt(1,"At left edge of document"); MsgEnd(); break;
   case  NoTextMarked :
            Prompt(1,"No Text Marked"); MsgEnd(); break;
   case  PBuffEmpty :
            Prompt(1,"Paste buffer empty"); MsgEnd(); break;
   case  TooNearTop :
            Prompt(1,"Too near top of document"); MsgEnd(); break;
   case  DocNotChanged :
            Prompt(1,"\""); Prompt(0,FName); Prompt(0,"\"");
            Prompt(0," Not changed ... Not written"); MsgEnd(); break;
   case  QuoteError :
            Prompt(1,"QUOTE ; abort  a  i  q  s  w  !cmd  number"); RingBell(); /* [?830] */
            MsgEnd(); break;
   case  ReadError :
            Prompt(0,"Read error"); MsgEnd(); break;
   case  WriteError :
            Prompt(0,"Write error"); MsgEnd(); break;
   case  NoCommandGiven :
            Prompt(1,"No command given"); MsgEnd(); break;
   case  OPNotImplemented :
            Prompt(1,"Not implemented"); RingBell(); MsgEnd(); break;
   case  SBuffEmpty :
            Prompt(1,"Search buffer empty"); MsgEnd(); break;
   case  ReadingFile :
            Prompt(1,"Reading "); Prompt(0,"\""); Prompt(0,PromptMsg); Prompt(0,"\"");
            Prompt(0," ... "); break;
   case  WritingFile :
            if   (Backup) { Prompt(0,"Writing "); }
            else          { Prompt(1,"Writing "); }
            Prompt(0,"\""); Prompt(0,PromptMsg); Prompt(0,"\""); Prompt(0," ... ");
            break;
   case  EditingFile :
            Prompt(1,EditorName); Prompt(0," Editing "); Prompt(0,"\"");
            Prompt(0,FName); Prompt(0,"\"");
```

<!-- PDF p.277 / printed p.xliv -->

```c
            if (DocChanged) { Prompt(0," *"); };
            PromptDisplayed=TRUE; PosImage(); break;
   case  EditingNewFile :
            Prompt(1,EditorName); Prompt(0," Editing ");  Prompt(0,"\"");
            Prompt(0,FName); Prompt(0,"\""); Prompt(0," (new file)");
            PromptDisplayed=TRUE; PosImage(); break;
   case  Done :
            Prompt(0,"Done"); MsgEnd(); break;
   case  UpdatingBackup :
            Prompt(1,"Updating "); Prompt(0,"\""); Prompt(0,PromptMsg); Prompt(0,"\"");
            Prompt(0," ... "); break;
   case  CannotUpdateBackup :
            Prompt(1,"Can't update "); Prompt(0,"\""); Prompt(0,PromptMsg);
            Prompt(0,"\""); Prompt(0," ... "); RingBell(); break;
   case  NoReadPermission :
            Prompt(1,"Read permission denied for "); Prompt(0,"\"");
            Prompt(0,PromptMsg); Prompt(0,"\""); MsgEnd(); break;
   case  Directory :
            Prompt(1,"\""); Prompt(0,PromptMsg); Prompt(0,"\"");
            Prompt(0," is a directory"); MsgEnd(); break; /* [?831] */
   case  FileNotExist :
            Prompt(1,"\""); Prompt(0,PromptMsg); Prompt(0,"\"");
            Prompt(0," does not exist"); MsgEnd(); break;
   case  CannotOpenFile :
            Prompt(1,"Can't open "); Prompt(0,"\""); Prompt(0,PromptMsg);
            Prompt(0,"\""); MsgEnd(); break;
   case  ShowQuotePrompt :
            Prompt(1,QuotePrompt); break;
   case  EditAborted :
            Prompt(1,"Edit aborted ... \""); Prompt(0,FName);
            Prompt(0,"\" Not written"); break;
   case  CntrlFound :
            Prompt(0," (Control chars discarded)"); RingBell(); MsgEnd(); break;
   case  HitKeyToResume :
            PosImage(); printf("\nHit <Return> to resume editing \"%s\"... ",FName); break;
   case  SearchingUpFor :
            Prompt(1,"Searching (up) for \""); Prompt(0,PromptMsg);
            Prompt(0,"\" ... "); break;
   case  SearchingDownFor :
            Prompt(1,"Searching (down) for \""); Prompt(0,PromptMsg);
            Prompt(0,"\" ... "); break;
   case  NotFound :
            Prompt(0,"Not found"); MsgEnd(); break;
   case  Found :
            Prompt(0,"Found"); MsgEnd(); break;
   case  Replaced :
            Prompt(1,"Replaced \""); Prompt(0,PromptMsg); Prompt(0,"\""); break;
   case  With :
            Prompt(0," With \""); Prompt(0,PromptMsg); Prompt(0,"\""); MsgEnd(); break;
   case  NotMatched :
            Prompt(1,"Not matched with \""); Prompt(0,PromptMsg); Prompt(0,"\"");
            MsgEnd(); break;
   case  ShowStats:
            Prompt(1,"Chars: "); GetAsString(Max+LP-RP); Prompt(0,PromptMsg);
            Prompt(0," \("); GetAsString(CP+1); Prompt(0,PromptMsg); Prompt(0,"\)");
            Prompt(0,"  Lines: "); GetAsString(DocNL+1); Prompt(0,PromptMsg); Prompt(0," \(");
            GetAsString(CurY); Prompt(0,PromptMsg); Prompt(0,"\)"); MsgEnd(); break;
   case  DBuffEmpty :
            Prompt(1,"Delete buffer empty"); MsgEnd(); break;
   case  Interrupted :
            Prompt(0," \(Interrupted\)"); RingBell(); MsgEnd(); break;
   case  Resumed :
            Prompt(0," \(Resumed\)"); MsgEnd(); break;
  }
```

<!-- PDF p.278 / printed p.xlv -->

```c
 fflush(stdout);
}
/* ------------------------------------------------------------------------------------- */
Prompt(curposn,msg)   int curposn;   char msg[];
{
 int prevPromptCur=PromptCur;   int ptr=0;   int count;
 if   (curposn==1) { PromptCur=1; }
 SetPromptCursor();
 while (PromptCur<WinWidth && msg[ptr]!='\0') { printf("%c",msg[ptr]); ptr++; PromptCur++; }
 count=PromptCur;
 while (count<prevPromptCur) { printf("%c",sp); count++; }
 SetPromptCursor();
}
/* ------------------------------------------------------------------------------------- */
MsgEnd()
{
 /* fflush(stdout); */ PromptDisplayed=FALSE;  PosImage();
}
/* ------------------------------------------------------------------------------------- */
SetPromptMsg(string)   char *string;
{
 strcpy(PromptMsg,string);
}
/* ------------------------------------------------------------------------------------- */
int GetAsString(num)   int num;
{
 char string[FNameMaxx];    CnvNumToString(num,string); SetPromptMsg(string);
}
/* ------------------------------------------------------------------------------------- */
```
