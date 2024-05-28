#【両端色付き付き正規表現から通常正規表現への変換 written by Akira Ito】
import bicrePARSERmodule, biCREtoREprepro, algorithm
import sequtils, tables, sugar #, strutils # for delete string
#import strutils
const availChars* = {' '..'~'} # == " !"#$%&'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\]^_`abcdefghijklmnopqrstuvwxyz{|}~"
const reservChars* = {'*','+','.','?','(',')','[',']','|','\"','\\'} #; const reservStrs* = @[":>",":>^","<:","<:_"] + @['\' & reservChars] 
#type NullFirstLast* = tuple[nullable: bool, first: seq[int], last: seq[int]] #!!
#type Tokenkind* = enum avachar, initpos, accpos, chclass, escchar, dotany, empstr #!!! decleared in biCREPARSERmodule (conflict)
proc toStr*(tokenseq: seq[(Tokenkind, string)]): string = # <== seq[(int, (Tokenkind, string))]
  var p = ""#r""
  for (tkind, tkstr) in tokenseq:
    case tkind
    of avachar: p &= tkstr
    of initpos: p &= ":>" & (if tkstr == "": "" else: "^") & tkstr 
    of accpos: p &= "<:" & (if tkstr == "": "" else: "_") & tkstr
    of chclass: p &= "[" & tkstr & "]"
    of escchar: p &= "\\" & tkstr #"\\" & tkstr #$'\\' & tkstr #"\\" & tkstr #r"\" & tkstr
    of dotany: p &= tkstr
    of empstr: p &= tkstr #"[]"
  return p # :>^R[+\-]:>^C[0-9]*(\.[0-9]|[0-9]<:_G\.)[0-9]*<:_B
proc toTokenseq(ptt: string): seq[(Tokenkind, string)] = 
  let (_, token) = biCREfollowtoken(ptt) # (_, Table[int, (Tokenkind, string)]) = (_, token function)
  return token.pairs.toSeq.sorted.mapIt(it[1])
proc times[T](s1,s2: seq[T]): seq[(T,T)] = # set[(T,T)] ==> ordinal type expected
  result = collect:
    for x in s1:
      for y in s2: (x,y)
proc findIniAccpos(tkseq: seq[(Tokenkind, string)]): (seq[int], seq[int]) = # pair of ini and acc position seqs 
  var iniposlist, accposlist: seq[int]
  (0..<tkseq.len).toSeq.filterIt(tkseq[it][0] == initpos).apply(proc(it: int) = iniposlist &= it)
  (0..<tkseq.len).toSeq.filterIt(tkseq[it][0] == accpos).apply(proc(it: int) = accposlist &= it)
  return (iniposlist, accposlist)
proc findLParenth(tkseq: seq[(Tokenkind, string)], i0: int): int = # search from i0-1. If not found retrun -1
  var j = i0 - 1
  var cnt = 1 # to identify same level as right parenthesis
  while (j >= 0):
    if tkseq[j] == (avachar, ")"): inc(cnt) elif tkseq[j] == (avachar, "("): dec(cnt)
    if cnt < 1: break
    dec(j)
  return j
proc findRParenth(tkseq: seq[(Tokenkind, string)], i0: int): int = # search from i0+1. If not found retrun s.len
  var j = i0 + 1 
  var cnt = 1 # to identify same level as left parenthesis # already parenthesis
  while (j < tkseq.len):
    if tkseq[j] == (avachar, "("): inc(cnt) elif tkseq[j] == (avachar, ")"): dec(cnt)
    if cnt < 1: break
    inc(j)
  return j
proc findRSumop(tkseq: seq[(Tokenkind, string)], i0: int): int = # search from i0+1. If not found retrun -1
  var j = i0 + 1
  while (j < tkseq.len): #    echo "j=",j
    if tkseq[j] == (avachar, "("): # skip over other parentheses
      j = findRParenth(tkseq, j); if j == tkseq.len: raise newException(IOError, "unbalanced parentheses") # not found ')' so not balanced
    elif tkseq[j] == (avachar, ")"): return -1 # reached at ')'
    elif tkseq[j] == (avachar, "|"): return j # found nearest '|'
    inc(j) # s[j] != '(' nor ')' nor '|'
  return j
proc findLSumop(tkseq: seq[(Tokenkind, string)], i0: int): int = # search from i0-1. If not found retrun -1
  var j = i0 - 1 
  while (j >= 0): #    echo "j=",j
    if tkseq[j] == (avachar, ")"): # skip over other parentheses
      j = findLParenth(tkseq, j); if j == -1: raise newException(IOError, "unbalanced parentheses") # not found '(' so not balanced
    elif tkseq[j] == (avachar, "("): return -1 # reached at '('
    elif tkseq[j] == (avachar, "|"): return j # found nearest '|'
    dec(j) # s[j] != '(' nor ')' nor '|'
  return j
proc simplifyEmpStr(tkseq0: seq[(Tokenkind, string)]): seq[(Tokenkind, string)] = # []*, []?, []+ ==> [] # thereafter exec eraseEmpStr() 
  var tkseq = tkseq0; var i = 0
  while (i < tkseq.len-1): # search empty string "[]" from left to right
    if tkseq[i][0] != empstr: inc(i); continue # else: "[]" found
    let rtk = tkseq[i+1]; if rtk == (avachar, "*") or rtk == (avachar, "?") or rtk == (avachar, "+"): tkseq.delete(i+1) else: inc(i)
  return tkseq
proc eraseEmpStr(tkseq0: seq[(Tokenkind, string)]): seq[(Tokenkind, string)] = # "[]" not being ([]),|[]),([]|,|[]| ==> ""
  var tkseq = tkseq0; var i = 0
  while (i < tkseq.len): # search "[]" from left to right #    echo "i=",i," tkseq=",tkseq
    if tkseq[i][0] != empstr: inc(i); continue # else: "[]" found
    if i-1 >= 0 and i+1 < tkseq.len: # at non-boudaries of tkseq
      let ltk = tkseq[i-1][1]; let rtk = tkseq[i+1][1]
      if (ltk,rtk) != ("(","|") and (ltk,rtk) != ("|",")") and (ltk,rtk) != ("|","|") and (ltk,rtk) != ("(",")"): tkseq.delete(i) else: inc(i)
    elif i == 0 and i+1 < tkseq.len: # at left boundary of tkseq
      let rtk = tkseq[i+1][1]; if rtk != "|": tkseq.delete(i) else: inc(i)
    elif i-1 >= 0 and i+1 == tkseq.len: # at right boundary of tkseq
      let ltk = tkseq[i-1][1]; if ltk != "|": tkseq.delete(i) else: inc(i)
    elif i == 0 and i+1 == tkseq.len: tkseq .delete(i) # when tkseq == "[]" 
  return tkseq
proc toStrseq(tkseqs: seq[seq[(Tokenkind, string)]]): seq[string] =  # "\." ==> @[..."\\."...]
  for tks in tkseqs: result &= tks.toStr
#[import lists
proc toStrlist(tkseqs: seq[seq[(Tokenkind, string)]]): SinglyLinkedList[string] =  # "\." ==> @[..."\\."...]
  result = initSinglyLinkedList[string]()
  for tks in tkseqs: result.add(tks.toStr)]#
proc echoTokenseqs(tkseqs: seq[seq[(Tokenkind, string)]]) = # replacement of "echo tkseqs.mapIt(it.toStr)"
  for i, tks in tkseqs: echo i,": \"", tks.toStr, "\""
proc toSStr*(tkseqs: seq[seq[(Tokenkind, string)]]): string = # replacement of "tkseqs.mapIt(it.toStr)"
  for i, tks in tkseqs: result &= $i & ": \"" & tks.toStr & "\"\n"

proc toREs*(ptt0: string): seq[seq[(Tokenkind, string)]] = # decomposition of biCRE to RE vector of indivisual ini & acc pairs
  # 0. resolve qmark,pmark operaters α?,α+ if α contains ini or acc position markers :>,<:
  let ptt = expandQmarkPmark(ptt0)
  let tkseq = ptt.toTokenseq   #echo "tkseq.toStr= ",": ", tkseq.toStr()
  # 1. make table of pairs-scattering seqs
  let (iposl0, aposl0) = findIniAccpos(tkseq) # make ini & acc state pos pairs list from token seq
  let pairposlist = iposl0.times(aposl0) #  echo iposl0," ", aposl0," ", pairposlist
  if pairposlist == @[]: return @[] # no pair, no expression
  var scttkseqtab = initTable[(int,int), seq[(Tokenkind, string)]]()
  for (j,i) in pairposlist:
    scttkseqtab[(j,i)] = @[]
    for it in 0..<tkseq.len: # all ini and acc markers deleted except the pair of jth ini and ith acc markers
      if it == j or it == i or (it notin iposl0 and it notin aposl0): scttkseqtab[(j,i)] &= tkseq[it]  #echo scttkseqtab.values.toSeq.mapIt(it.toStr)
  var scttkseqs = scttkseqtab.values.toSeq  #echo "scttkseqs.toStr= ",scttkseqs.mapIt(it.toStr) # "\." ==> @[..."\\."...]
  #echo "scattered tkseqs= "; echoTokenseqs(scttkseqs); echo scttkseqs.toSStr
  var newscttkseqs: seq[seq[(Tokenkind, string)]]
  # 2. make new token seqs in which all pos markers are evicted from star loops
  while (true): # newscttkseqs != scttkseqs # fixed-point computation    #echo "scttkseqs= ",scttkseqs.mapIt(it.toStr)
    for tks in scttkseqs: # for each pair-scattered token seq #      echo "tks= ",tks.toStr
      let (iposl, aposl) = findIniAccpos(tks); let (ipos, apos) = (iposl[0], aposl[0]) # assume iposl,aposl has unique element #      echo "ipos= ",ipos," apos= ", apos
      # 2.1 find star loops
      var stars: seq[int]; (0..<tks.len).toSeq.filterIt(tks[it] == (avachar,"*")).apply(proc(it: int) = stars &= it) # assume no +,? operator #      echo "stars= ",stars
      var stloops: seq[(int,int)] # range of star operater including (possible) parehtheses
      for k in stars:
        if tks[k-1] == (avachar,")"): stloops &= (tks.findLParenth(k-1), k-1)
        else: stloops &= (k-1, k-1) #       echo "stloops= ",stloops
      # 2.2 find the outermost starloop for ini,acc position markers :>((a<:b)*c)* ==> :>((ab)*c)*((a<:b)*c)
      let iposloops = stloops.filterIt(it[0] <= ipos and ipos <= it[1]) #      echo "iposloops= ",iposloops
      let il = if iposloops == @[]: (-1,-1) else: iposloops[iposloops.mapIt(it[1]-it[0]).maxIndex]
      let aposloops = stloops.filterIt(it[0] <= apos and apos <= it[1]) #      echo "aposloops= ",aposloops
      let al = if aposloops == @[]: (-1,-1) else: aposloops[aposloops.mapIt(it[1]-it[0]).maxIndex] #       echo "il: ",il," al: ",al
      # 2.3 eviction of one depth
      let etk: seq[(Tokenkind, string)] = @[(empstr, "[]")]
      if il == (-1,-1) and al == (-1,-1): newscttkseqs &= tks # neither ini nor acc marker is in a star loop: no change
      elif il == al: # (1) both ini and acc markers are in the same star loop T[α[:>,<:]*] ==> T[α[:>,<:]] ++ T[α[:>,ε]α[ε,ε]*α[ε,<:]]
        let alpha = tks[il[0]..il[1]]; let pref = tks[0..<il[0]]; let suff = tks[il[1]+1..<tks.len]
        newscttkseqs &= pref & alpha & suff[1..<suff.len] # ony without star symbol
        let alpha0a = tks[il[0]..<apos] & etk & tks[apos+1..il[1]]; let alpha0i = tks[al[0]..<ipos] & etk & tks[ipos+1..al[1]]
        let alpha0ia = if ipos < apos: tks[il[0]..<ipos] & etk & tks[ipos+1..<apos] & tks[apos+1..il[1]] else: tks[il[0]..<apos] & etk & tks[apos+1..<ipos] & tks[ipos+1..il[1]]
        newscttkseqs &= pref & alpha0a & alpha0ia & (avachar,"*") & alpha0i & suff[1..<suff.len]
      elif il != (-1,-1) and al == (-1,-1): # (2) ini marker is in a star loop T[α[:>]*] ==> T[α[:>]α[ε]*]
        let alpha = tks[il[0]..il[1]]; let alpha0 = if il[0] != il[1]: tks[il[0]..<ipos] & etk & tks[ipos+1..il[1]] else: etk # for :>*, :>+
        let pref = tks[0..<il[0]]; let suff = tks[il[1]+1..<tks.len]
        newscttkseqs &= pref & alpha & alpha0 & (avachar,"*") & suff[1..<suff.len]
      elif il == (-1,-1) and al != (-1,-1): # (3) acc marker is in a star loop T[α[<:]*] ==> T[α[ε]*α[<:]]
        let alpha = tks[al[0]..al[1]]; let alpha0 = if al[0] != al[1]: tks[al[0]..<apos] & etk & tks[apos+1..al[1]] else: etk # for <:*, <:+
        let pref = tks[0..<al[0]]; let suff = tks[al[1]+1..<tks.len]
        newscttkseqs &= pref & alpha0 & (avachar,"*") & alpha & suff[1..<suff.len]
      else: #il != (-1,-1) and al != (-1,-1): # (4) ini and acc markers are in separated loops T[α[:>]*,β[<:]*] ==> T[α[:>]α[ε]*,β[ε]*β[<:]]
        let alpha = tks[il[0]..il[1]]; let alpha0 = if il[0] != il[1]: tks[il[0]..<ipos] & etk & tks[ipos+1..il[1]] else: etk # for :>*, :>+
        let beta = tks[al[0]..al[1]]; let beta0 = if al[0] != al[1]: tks[al[0]..<apos] & etk & tks[apos+1..al[1]] else: etk # for <:*, <:+
        if ipos < apos:
          let pref = tks[0..<il[0]]; let cent = tks[il[1]+1..<al[0]]; let suff = tks[al[1]+1..<tks.len]
          newscttkseqs &= pref & alpha & alpha0 & (avachar,"*") & cent[1..<cent.len] & beta0 & (avachar,"*") & beta & suff[1..<suff.len]
        else: # apos < ipos:
          let pref = tks[0..<al[0]]; let cent = tks[al[1]+1..<il[0]]; let suff = tks[il[1]+1..<tks.len]
          newscttkseqs &= pref & beta0 & (avachar,"*") & beta & cent[1..<cent.len] & alpha & alpha0 & (avachar,"*") & suff[1..<suff.len]
      # end of scttkseqs loop #    echo "newscttkseqs= ",newscttkseqs.mapIt(it.toStr)
    if scttkseqs == newscttkseqs: newscttkseqs = @[]; break # reached at fixed-point
    scttkseqs = newscttkseqs; newscttkseqs = @[]
  # end of while fixe-point  #  echo "evicted scttkseqs.toStr= ",scttkseqs.mapIt(it.toStr)   #  echo "evicted scttkseqs= ",scttkseqs
# 3. peel usless peripheral strings
  for tks0 in scttkseqs:
    var tks = tks0 #: seq[(Tokenkind, string)]
    # 3.1 peel left peripheral
    let (iposl, _) = findIniAccpos(tks); if iposl == @[]: continue # no ini pos, skip to next tks 
    var ipos = iposl[0] # assume iposl has unique element #    echo "tks= ", tks; echo "ipos= ",ipos
    while true:
      # delete seg from left parenth included (or left end) to ini pos marker exluded
      let lp = tks.findLParenth(ipos)
      if lp == -1: tks = tks[ipos..<tks.len]; ipos = 0; break # left parenth '(' not found and reached at left end: go to right peeling
      tks = tks[0..<lp] & tks[ipos..<tks.len]; ipos = lp # preserve the other segs
      let rp = tks.findRParenth(ipos); if rp == tks.len: raise newException(IOError, "unbalanced parentheses") # ')' not found, not balanced
      # delete seg from sum operater (if any) included to right parenth included
      var rs = tks.findRSumop(ipos) # skip to right '|'
      if rs == -1: rs = rp # rightward sum op '|' not found and reached at right parenth ')': regard ')' as '|'
      tks = tks[0..<rs] & tks[rp+1..<tks.len] # preserve the other segs
    # 3.2 peel right peripharal
    let (_, aposl) = findIniAccpos(tks); if aposl == @[]: continue # no acc pos, skip to next tks
    var apos = aposl[0] # assume aposl has unique element #      
    while true:
      # delete seg from acc pos marker exluded to right parenth included (or right end)
      let rp = tks.findRParenth(apos)
      if rp == tks.len: tks = tks[0..apos]; break # right parenth ')' not found and reached at right end: current tks completed
      tks = tks[0..apos] & tks[rp+1..<tks.len] # preserve the other segs
      let lp = tks.findLParenth(apos); if lp == -1: raise newException(IOError, "unbalanced parentheses") # '(' not found, not balanced
      # delete seg from sum operater (if any) included to left parenth included
      var ls = tks.findLSumop(apos) # skip to left '|'
      if ls == -1: ls = lp # rightward sum op '|' not found and reached at left parenth '(': regard '(' as '|'
      tks = tks[0..<lp] & tks[ls+1..<tks.len]; apos -= ls - lp + 1 # preserve the other segs
    newscttkseqs &= tks #    echo "peeled newscttkseqs.toStr= ",newscttkseqs.mapIt(it.toStr) #    echo "peeled newscttkseqs= ",newscttkseqs
  #let newptts = newscttkseqs.mapIt(it.toStr) # @[ptt]
  # 4. erase & simplify empty strings & deduplicate
  return newscttkseqs.mapIt(it.simplifyEmpStr.eraseEmpStr).deduplicate #.mapIt(it.toStr)

when isMainModule:
  var ptt = r":>^R[+-]:>^C[0-9]*(\.[0-9]|[0-9]<:_G\.)[0-9]*<:_B" # r":>(0|1)*1(0|1)<:(0|1)<:" # r":>(0?0?<:1)*" # 
  # r":>(0|1(<:_101*<:_20|11)*1<:_30)*<:_0" #=>@[":>(0|1(01*0|11)*10)*<:_0", ":>(0|1(01*0|11)*10)*1(01*0|11)*01*<:_2", ":>(0|1(01*0|11)*10)*1(01*0|11)*<:_1", ":>(0|1(01*0|11)*10)*1(01*0|11)*1<:_3"]
  # r":>((0|(0|1<:_B0)(000<:_B0)*001)(<:_R1(0<:_G00<:_B0)*0<:_G01)*<:_R0)*(0|1<:_B0)(000<:_B0)*0<:_G" #=>@["
  #":>((0|(0|10)(0000)*001)(1(0000)*001)*0)*(0|(0|10)(0000)*001)(1(0000)*001)*1(0000)*0<:_G", 
  #":>((0|(0|10)(0000)*001)(1(0000)*001)*0)*(0|10)(0000)*000<:_B", 
  #":>((0|(0|10)(0000)*001)(1(0000)*001)*0)*(0|10)(0000)*0<:_G", 
  #":>((0|(0|10)(0000)*001)(1(0000)*001)*0)*(0|(0|10)(0000)*001)(1(0000)*001)*<:_R", 
  #":>((0|(0|10)(0000)*001)(1(0000)*001)*0)*1<:_B", 
  #":>((0|(0|10)(0000)*001)(1(0000)*001)*0)*(0|(0|10)(0000)*001)(1(0000)*001)*1(0000)*000<:_B"]
  # r":>((aa|bb)*<:(ab|ba)(aa|bb)*(ab|ba))*" #=> @[":>((aa|bb)*(ab|ba)(aa|bb)*(ab|ba))*(aa|bb)*<:"] # r"((b:><:b|aa)*(b:><:a|ab)(a:><:a|bb)*(a:><:b|ba))*" #=> @[":>a(aa|bb)*(ab|ba)((bb|aa)*(ba|ab)(aa|bb)*(ab|ba))*(bb|aa)*b<:", ":><:", ":>a(aa|bb)*a<:", ...
  # r"a|b(c|d(e:>|f(<:g)*)*)*"#=> @[":>(e|f(g)*)*f(g)*<:", ":>(e|f(g)*)*(c|d(e|f(g)*)*)*d(e|f(g)*)*f(g)*<:"]
  # r"(j(a|b:>c|i)(d|e)(f<:g|h)k)" # r"a|b(c|d(e:>|f(g)*(<:g)))"#=>@[] # r"a|b(c|d(e:>|f(g)*)(e|f(g)*)*(e|f(g)*(<:g)))"#=>@[":>(e|f(g)*)*f(g)*<:"] # r"a|b(c|d(e:>|f(g)*)(e|f(g)*)*)(c|d(e|f(g)*)*)*(c|d(e|f(g)*)*(e|f(g)*(<:g)))"#=>@[":>(e|f(g)*)*(c|d(e|f(g)*)*)*d(e|f(g)*)*f(g)*<:"] # 
  # r"(a:>b)*c(d<:e)*" # r"f(a(b:>c)*d<:e)*g" # r":>a(:>b<:)*"#=>@[":>a(b)*b<:", ":>b<:", ":>b(b)*b<:"] # r":>((a<:b)*c)*"#=>":>((ab)*c)*(ab)*a<:" #  
  # r":>*<:*"#=>":><:" # r":><:*"#=>":><:" # r":>*<:"#=>":><:" # r"(<::>)*"#=>":>([])*<:" # r"(<:|:>)*"#=>":>([]|)*<:" # r"(0<::>1)*"#=>":>1(01)*0<:" # r"(0:><:1)*"#=>@[":><:", ":>1(01)*0<:"] # r"(0*<:2:>1*)*"#=>":>1*(0*21*)*0*<:" # r":>(0:><:1)*<:"#=>@[":><:", ":>1(01)*0<:", ":>1(01)*<:", ":>(01)*0<:", ":>(01)*<:"] # 
  # r"a|b(c|d(e:>|f(<:g)*)*)*" # ==> @[":>(e|f(g)*)*f(g)*<:", ":>(e|f(g)*)*(c|d(e|f(g)*)*)*d(e|f(g)*)*f(g)*<:"]
  # r"(a(b:>a*<:b)*a|b)*" # ==> @[":>a*<:", ":>a*b(ba*b)*ba*<:", ":>a*b(ba*b)*a(a(ba*b)*a|b)*a(ba*b)*ba*<:"]
  # r":>((a<:_1b)*c<:_2)*"#ε# # r"(a:>(b<:c)*)*"#ε# # r":>((a<:b)*c)*"#ε# # r":>^1a<:_1b:>^2c<:_2d:>^1e<:_1"#editor's example # r"(a<:(b:>c)*)*"#ε# 
  # r"(a|:>b)*<:"#ε# # r":>([A-Z][a-z]*<: )*"#ε# # r":>x([w]([w-]+[w])?<: )*"#ε# # r":>(0|1(<:_B01*<:_C0|11)*1<:_D0)*<:_A"#ε# # 
  echo "biCRE pattern = ", ptt #  echo $(ptt.toREs.toStrlist)  #echo toREs(ptt).mapIt(it.toStr) # @[":>^C[0-9]*[0-9]<:_G", ":>^R[+-][0-9]*(\\.[0-9]|[0-9]\\.)[0-9]*<:_B", ":>^R[+-][0-9]*[0-9]<:_G", ":>^C[0-9]*(\\.[0-9]|[0-9]\\.)[0-9]*<:_B"]
  #echoTokenseqs toREs(ptt)
  echo toREs(ptt).toSStr
