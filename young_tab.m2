-- computes skew Hall-Littlewoods via tableau
-- decomposes Q_{lam/mu} as a linear combination of Q_nu


restart

largestIndex = 20

R = QQ[t][x_1..x_largestIndex]

needsPackage "SpechtModule"

protect symbol x
protect symbol R
protect symbol largestIndex


---------- SSYT

-- tableau T is equiv to sequence of partitions
-- returns list of partitions mu=lam^0,lam^1,...,lam^r=lam (mu is the shape made by 0s)
tabToPartSeq = T -> (
    for i from 0 to (max entries T) list (
        --print("tabToPartSeq: "|(net T));
        for j from 0 to (numRows T - 1) list (
            number(T^j,k -> k<=i)
            )
        )
    )

-- returns conjugate of lam
conj = lam -> (
    if lam == {} then return {0};
    ans = for i from 1 to (lam#0) list number(lam, k -> k>=i);
    if ans == {} then (ans = {0});
    ans
    )


-- appends 0's to the end of lam
appendZeros = (lam,num) -> (
    for i from 0 to #lam+num-1 list (
        if i < #lam then (lam#i) else (0)
        )
    )

-- generate 'largest' SSYT of shape lam/mu
maxSSYT = (lam,mu) -> (
    ans := {};
    muE := appendZeros(mu,#lam-#mu);
    
    currRow := {};
    for j from 0 to lam#0-1 do (
        Tij := 0;
        if j >= muE#0 then (Tij = 1;);
        currRow = append(currRow,Tij);
        );
    ans = append(ans,currRow);
    
    for i from 1 to #lam-1 do (
        currRow := {};
        for j from 0 to lam#i-1 do (
            Tij := ans#-1#j+1;
            if j < muE#i then (Tij = 0;);
            currRow = append(currRow,Tij);
            );
        ans = append(ans,currRow);
        );
    theLam := new Partition from lam;
    youngTableau(theLam,flatten ans)
    )

-- generate 'smallest' SSYT of shape lam/mu, with max entry
minSSYT = (lam,mu,maxEntry) -> (
    lam' := conj lam;
    mu' := conj mu;
    mu' = appendZeros(mu',#lam'-#mu');
    
    for i from 0 to #lam'-1 do (
        if lam'#i-mu'#i > maxEntry then (
            print("maxSSYT: maxEntry too small");
            return {};
            );
        );
    
    ans := {};
    
    muE := appendZeros(mu,#lam-#mu);
    
    for i from 0 to #lam-1 do (
        currRow := {};
        for j from 0 to (lam#i)-1 do (
            Tij := maxEntry-lam'#j+i+1;
            if j < muE#i then (Tij = 0;);
            currRow = append(currRow,Tij);
            );
        ans = append(ans,currRow);
        );
    theLam := new Partition from lam;
    youngTableau(theLam,flatten ans)
    )

-- adds 1 to index (rowIndex,colIndex), and to other indices below/right
addOneSSYT = (T,rowIndex,colIndex,maxEntry,minSSYT) -> (
    seq := tabToPartSeq T;
    lam := seq#-1;
    mu := seq#0;
    muE := appendZeros(mu,#lam-#mu);
    
    if (rowIndex < 0) or (rowIndex >= #lam) then return;
    if (colIndex < muE#rowIndex) or (colIndex >= lam#rowIndex) then return;
    
    ans := for i from 0 to rowIndex-1 list T^i;
    
    maxColIndex := 0;
    for currRowIndex from rowIndex to (#lam-1) do (
        theRow := new MutableList from T^currRowIndex;
        prevRow := for i from 0 to #theRow-1 list 0;
        if currRowIndex > 0 then (prevRow = ans#-1);
        for currColIndex from colIndex to #theRow-1 do (
            Tij := theRow#currColIndex;
            if (currRowIndex == rowIndex) and (currColIndex == colIndex) then (
                Tij = Tij + 1;
                ) else if currColIndex == 0 then (
                if Tij <= prevRow#0 then (Tij = Tij + 1);
                ) else (
                if (Tij <= prevRow#currColIndex) or (Tij < theRow#(currColIndex-1)) then (
                    Tij = Tij+1;
                    );
                );
            
            if (Tij > minSSYT^currRowIndex#currColIndex) or (Tij > maxEntry) then (
                return;
                );
            theRow#currColIndex = Tij;
            );
        ans = append(ans,new List from theRow);
        );
    listToTableau ans
    )

-- converts an index in 1..(weight(lam\mu)) to its row and column indices
-- indices in answer start from 0
indToRowIndColInd = (lam,mu,ind) -> (
    mu' := appendZeros(mu,#lam-#mu);
    ans := listToTableau for i from 0 to #lam-1 list for j from 0 to lam#i-1 list (
        if j < mu'#i then (0) else (1)
        );
    
    counter := 1;
    
    for i from 1 to lam#0 do (for j from 1 to #ans_(lam#0-i) do (
            if ans_(lam#0-i)#(#ans_(lam#0-i)-j) > 0 then (
                if counter == ind then return (#ans_(lam#0-i)-j,lam#0-i);
                ans_(#ans_(lam#0-i)-j,lam#0-i) = counter;
                counter = counter + 1;
                );
            );
        );
    
    print("error: index too large");
    
    ans
    )

-- generate list of all SSYT of shape lam/mu, with max entry n
genAllSSYT = (lam,mu,maxEntry) -> (
    lam' := conj lam;
    mu' := conj mu;
    mu' = appendZeros(mu',#lam'-#mu');
    
    -- check if maxEntry is large enough
    for i from 0 to #lam'-1 do (
        if lam'#i-mu'#i > maxEntry then (
            return {};
            );
        );
    
    maxT := maxSSYT(lam,mu);
    minT := minSSYT(lam,mu,maxEntry);
    ans := {maxT};
    
    recurse := (T,ind) -> (
        
        inds := indToRowIndColInd(lam,mu,ind);
        rowIndex := inds#0;
        colIndex := inds#1;
        
        newT := addOneSSYT(T,rowIndex,colIndex,maxEntry,minT);
        
        if not instance(newT,Nothing) then (
            ans = append(ans,newT);
            
            for i from 1 to ind do (
                recurse(newT,i)
                );
            );
        );
    
    for theInd from 1 to ((sum lam) - (sum mu)) do (
        recurse(maxT,theInd);
        );
    
    ans
    )

-- returns true if theT is an SSYT
isSSYT = theT -> (
    listT := tableauToList theT;
    for theRow in listT do (
        if theRow != sort theRow then (
            return(false);
            );
        );
    
    for i from 0 to #(listT#0)-1 do (
        theCol := theT_i;
        for j from 0 to #theCol-2 do (
            if theCol#j != 0 and theCol#j >= theCol#(j+1) then return(false);
            );
        );
    
    return true;
    )

-- outputs theT into ytableau package
-- rows that are not weakly decreasing are in red
-- columns not strictly increasing are in green
tabToTex = theT -> (
    ans := "\\begin{ytableau}\n";
    
    listT := tableauToList theT;
    
    for i from 0 to #listT-1 do (
        theRow := listT#i;
        line := "    ";
        
        for j from 0 to #theRow-1 do (
            theBox := theRow#j;
            if theBox == 0 then (
                line = line|"\\none"|"&";
                ) else (
                currCol := theT_j;
                
                boxColor := "";
                if 2 <= i and theBox <= currCol#(i-1) then (
                    boxColor = "*(green)";
                    );
                if 0 < i and i <= #currCol-2 and theBox >= currCol#(i+1) then (
                    boxColor = "*(green)";
                    );
                if theRow != sort theRow then (
                    boxColor = "*(red)";
                    );
                
                line = line|boxColor|toString(theBox)|"&";
                );
            );
        ans = ans|substring(line,0,#line-1)|"\\\\\n";
        );
    ans = ans|"\\end{ytableau}";
    
    ans
    )

---------- Hall-Littlewood functions

-- returns the monomial x^T, where T is a tableau
TtoxT = T -> (
    product for entry in flatten tableauToList T list (
        if entry > 0 then (x_entry) else (1)
        )
    )

-- returns a list of partitions from reordering a composition [Macdonald p.214]
reorderPart = lam -> (
    ans := {};
    
    reorderOnce := (theLam,theCoeff) -> (
        if rsort lam == lam then (
            ans = append(ans,(theLam,theCoeff));
            return {lam};
            );
        for i from 0 to #theLam-2 do (
            if theLam#i < theLam#(i+1) then (
                lamSwitch := switch(i,i+1,theLam);
                Rij := for k from 0 to #theLam-1 list (
                    if k == i then (-1)
                    else if k == i+1 then (1)
                    else (0)
                    );
                r := theLam#(i+1);
                s := theLam#(i);
                
                m := (r-s)//2;
                if (r-s)%2 == 1 then (
                    m = (r-s-1)//2;
                    );
                
                for i from 0 to m do (
                    newLam := lamSwitch + i*Rij;
                    newCoeff := t;
                    if i > 0 then (
                        newCoeff = t^(i+1)-t^(i-1);
                        );
                    if i == m and (r-s)%2 == 0 then (
                        newCoeff = t^m-t^(m-1);
                        );
                    --if newLam#-1 < 0 then continue;
                    if rsort newLam == newLam then (
                        ans = append(ans,(newLam,theCoeff * newCoeff));
                        ) else (
                        reorderOnce(newLam,theCoeff * newCoeff);
                        );
                    );
                return();
                );
            );
        );
    
    reorderOnce(lam,1);
    
    
    -- combine coefficients
    ans2 := {ans#0};

    for i from 1 to #ans-1 do (
        if ans2#-1#0 == ans#i#0 then (
            ans2 = replace(-1,(ans#i#0,ans2#-1#1 + ans#i#1),ans2);
            ) else (
            ans2 = append(ans2,ans#i);
            );
        );
    
    ans2
    )

-- returns x^lam
xLam = lam -> (
    if #lam == 0 then return 1;
    product for i from 1 to #lam list x_i^(lam#(i-1))
    )

---------- bijection


genhsSSYT = (n,lam,i) -> (
    if i > #lam then return({});
    hSSYT := genAllSSYT({n+i},{0},#lam+1);
    sSSYT := genAllSSYT(lam,toList(i:1),#lam+1);
    ans := {};
    
    for hT in hSSYT do (
        for sT in sSSYT do (
            ans = ans|{listToTableau(tableauToList(hT)|tableauToList(sT))};
            );
        );
    ans
    )


-- returns true if the first row is weakly increasing, and other rows form an SSYT
ishsSSYT = theT -> (
    if not instance(theT,YoungTableau) then return(false);
    listT := tableauToList theT;
    
    if listT#0 != sort listT#0 then return(false);
    
    return(isSSYT listToTableau(listT_{1..(#listT-1)}));
    )

--moves first box of row i to row 0, shifting row 0 right
moveBoxUp = (theT,i) -> (
    listT := tableauToList theT;
    numRows := #listT;
    if i <= 0 or i > numRows-1 then return(theT);
    
    newList := {{theT_(i,0)}|listT#0};
    for j from 1 to numRows-1 do (
        if j == i then (
            newList = newList|{{0}|(listT#j)_{1..(#(listT#j)-1)}};
            ) else (
            newList = newList|{listT#j};
            );
        );
    
    listToTableau newList
    )

-- swap first k boxes of row i with first k-1 boxes of row 0, shifting row 0 right
moveMultiBoxUp = (theT,i,k) -> (
    listT := tableauToList theT;
    numRows := #listT;
    
    
    theRow0 := theT^0;
    theRowi := theT^i;
    
    if k >= #theRow0 or k > #theRowi then return(false);
    if i <= 0 or i > numRows-1 then return(theT);
    if k == 0 then return(theT);
    
    startRow0 := theRow0_{0..(k-2)};
    endRow0 := theRow0_{(k-1)..(#theRow0-1)};
    startRowi := theRowi_{0..(k-1)};
    endRowi := theRowi_{k..(#theRowi-1)};
    
    newList := {startRowi|endRow0};
    for j from 1 to numRows-1 do (
        currRow := {};
        if j == i then (
            currRow = {0}|startRow0|endRowi;
            ) else (
            currRow = listT#j;
            );
        newList = newList|{currRow};
        );
    
    listToTableau newList
    )

-- swap first k boxes of row 0 with first k-1 boxes of row i, shifting row 0 left
moveMultiBoxDown = (theT,i,k) -> (
    listT := tableauToList theT;
    numRows := #listT;
    
    
    theRow0 := theT^0;
    theRowi := theT^i;
    
    if k >= #theRow0 or k > #theRowi then return(false);
    if i <= 0 or i > numRows-1 then return(theT);
    if k == 0 then return(theT);
    if theRowi#0 != 0 then print("Warning: should be 0 in first entry of row i");
    
    startRow0 := theRow0_{0..(k-1)};
    endRow0 := theRow0_{k..(#theRow0-1)};
    startRowi := theRowi_{1..(k-1)};
    endRowi := theRowi_{k..(#theRowi-1)};
    
    newList := {startRowi|endRow0};
    for j from 1 to numRows-1 do (
        currRow := {};
        if j == i then (
            currRow = startRow0|endRowi;
            ) else (
            currRow = listT#j;
            );
        newList = newList|{currRow};
        );
    
    listToTableau newList
    )

--moves first box of row 0 to row i, shifting row 0 left
moveBoxDown = (theT,i) -> (
    if i <= 0 then return(theT);
    listT := tableauToList theT;
    numRows := #listT;
    if i <= 0 or i > numRows-1 then return(theT);
    
    newList := {(listT#0)_{1..(#(listT#0)-1)}};
    for j from 1 to numRows-1 do (
        if j == i then (
            newList = newList|{{theT_(0,0)}|(listT#j)_{1..(#(listT#j)-1)}};
            ) else (
            newList = newList|{listT#j};
            );
        );
    
    listToTableau newList
    )

-- if theT_(i,0) == 0 then: swaps first k-1 boxes of row i with the first k   boxes of row 0
--                    else: swaps first k   boxes of row i with the first k-1 boxes of row 0
swapRows = (theT,i,k) -> (
    listT := tableauToList theT;
    
    if i == 0 or k == 0 then return(theT);
    if i >= #listT then return(false);
    
    theRow0 := theT^0;
    theRowi := theT^i;
    
    if k > #theRowi then return(false);
    
    isSkew := theRowi#0 == 0;
    skewOffset := 0;
    if isSkew then (skewOffset = 1);
    
    startRow0 := theRow0_{0..(k-2+skewOffset)};
    endRow0 := theRow0_{(k-1+skewOffset)..(#theRow0-1)};
    startRowi := theRowi_{0..(k-1)};
    endRowi := theRowi_{k..(#theRowi-1)};
    
    extraBox := {0};
    if isSkew then (
        extraBox = {};
        startRowi = startRowi_{1..#startRowi-1};
        );
    
    newRow0 := startRowi|endRow0;
    newRowi := extraBox|startRow0|endRowi;
    
    newList := {newRow0};
    for j from 1 to #listT-1 do (
        if j == i then (
            newList = newList|{newRowi};
            ) else (
            newList = newList|{theT^j};
            );
        );
    
    listToTableau newList
    )


-- moves first box from row i to row 0
theMap = (theT) -> (
    firstCol := theT_0;
    numZeros := number(firstCol,theBox -> theBox == 0);
    i := numZeros + 1;
    
    if i == 1 and isSSYT(theT) then return(theT);
    
    listT := tableauToList theT;
    numRows := #listT;
    
    mapAddT := listToTableau {{2,1}};--swapRows(theT,numZeros,1);
    mapRemT := listToTableau {{2,1}};--swapRows(theT,numZeros+1,1);
    
    --print(net mapAddT);
    --print(net mapRemT);
    --print(i);
    
    --if i == 1 then return(mapRemT);
    --if i == #firstCol then return(mapAddT);
    
    for k from 1 to min(#(listT#0),#(listT#(i-1))) do (
        if i != 1 then (
            mapAddT = swapRows(theT,numZeros,k);
            );
        if i != #firstCol then (
            mapRemT := swapRows(theT,numZeros+1,k);
            );
        
        if ishsSSYT(mapAddT) and i != 1 then (
            return(mapAddT);
            ) else if ishsSSYT(mapRemT) and i != #firstCol then (
            return(mapRemT);
            )
        );
    
    return(listToTableau {{2,1}});
    )


-*

test2 = listToTableau {{2,2,2,2},{0,1,1},{3,3,3}}
net test2
net theMap test2

min(1,2,3)


aT = listToTableau {{1,2,3,4,5,6},{11,22,33,44},{111,222,333,444},{1111,2222,3333}}
bT = listToTableau {{1,2,3,4,5,6},{0,22,33,44},{0,222,333,444},{0,2222,3333}}

rowInd = 2
numBox = 3

net aT
net swapRows(aT,rowInd,numBox)
net theMap(aT)

net bT
net swapRows(bT,3,1)
net theMap(bT)
*-

-- moves first box from row i to row 0
theMapOld = (theT,i) -> (
    if i == 1 and isSSYT(theT) then return(theT);
    
    listT := tableauToList theT;
    numRows := #listT;
    
    if i > numRows then print("theMap error: i too large");
    if i == numRows then return(theT);
    
    upT := moveBoxUp(theT,i)
    --downT := moveBoxDown(theT,i);
    )



theMapAllOld = (n,lam) -> (
    tabList := {};
    mapList := {};
    --mapUpList := {};
    --mapDownList := {};
    
    for i from 0 to #lam do (
        currTabList := {};
        currMapList := {};
        --currMapUpList := {};
        --currMapDownList := {};
        
        thehsList := genhsSSYT(n,lam,i);
        
        for theT in thehsList do (
            currTabList = currTabList|{theT};
            --print(net theT);
            currMapList = currMapList|{theMap(theT)};
            --currMapUpList = currMapUpList|{moveBoxUp(theT,i+1)};
            --currMapDownList = currMapDownList|{moveBoxDown(theT,i)};
            );
        tabList = tabList|{currTabList};
        mapList = mapList|{currMapList};
        --mapUpList = mapUpList|{currMapUpList};
        --mapDownList = mapDownList|{currMapDownList};
        );
    
    ans := "";
    for i from 0 to #tabList-1 do (
        textPair := "";
        for j from 0 to #(tabList#i)-1 do (
            theT := tabList#i#j;
            theMapT := mapList#i#j;
            --theMapUpT := mapUpList#i#j;
            --theMapDownT := mapDownList#i#j;
            
            textPair = "\\[\n";
            textPair = textPair|tabToTex(theT);
            if theT != theMapT then (
                textPair = textPair|"\n\\qquad\n";
                textPair = textPair|tabToTex(theMapT);
                );
            -*
            if i < #tabList-1 then (
                textPair = textPair|"\n\\qquad\n";
                textPair = textPair|tabToTex(theMapUpT);
            );
            if i > 0 then (
                textPair = textPair|"\n\\qquad\n";
                textPair = textPair|tabToTex(theMapDownT);
            );
            *-
            
            textPair = textPair|"\n\\]\n";
            if i > 0 and number(mapList#(i-1),aT -> aT == theT) == 0 then (
                textPair = textPair|"\\begin{center}\\hl{Above Not Cancelled}\\end{center}\n";
                );
            ans = ans|textPair;
            ans = ans|"\\vspace{1em}\n";
            );
        
        );
    
    ans
    )




n = 3
lam = {3,2,2}
theMapAllOld(n,lam)




test = genhsSSYT(n,lam,0)
#test

ans = ""
for theT in test do (
    print(net moveBoxUp(theT,1));
    )
ans

aT = listToTableau {{2,2,3,3},{0,1,1},{3,3}}

#test
number(test2,i -> i == aT)
test#0 == test#1
net test#0
net test#1




test = genAllSSYT(lam,{0},#lam)


aT = listToTableau {{1,2,3,4,5,6},{11,22,33,44},{111,222,333,4444},{1111,2222,3333}}
net aT
net moveMultiBoxUp(aT,2,4)
ishsSSYT aT

net aT
swapRows(aT,2,2)




aT = listToTableau {{1,2,3,4,5,6},{11,22,33,44},{111,222,333,444},{1111,2222,3333}}
bT = listToTableau {{1,2,3,4,5,6},{0,22,33,44},{0,222,333,444},{0,2222,3333}}

rowInd = 2
numBox = 5

net aT
net swapRows(aT,rowInd,numBox)

net bT
net swapRows(bT,rowInd,numBox)











