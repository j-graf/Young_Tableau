-- computes skew Hall-Littlewoods via tableau
-- decomposes Q_{lam/mu} as a linear combination of Q_nu


restart

largestIndex = 20
maxWt = 48 --max ~50

S = QQ[t][for thePart in rsort join(for i from 0 to maxWt list toSequence({i}),flatten for i from 0 to maxWt list for j from 1 to min(i,maxWt-i) list (i,j),flatten flatten for i from 0 to maxWt list for j from 1 to min(i,maxWt-i) list for k from 1 to min(j,maxWt-i-j) list (i,j,k)) list (
        if #thePart == 1 then (Q_(thePart#0))
        else if #thePart == 2 then (Q_(thePart#0,thePart#1))
        else if #thePart == 3 then (Q_(thePart#0,thePart#1,thePart#2))
        )]
R = QQ[t][x_1..x_largestIndex]

needsPackage "SpechtModule"

protect symbol x
protect symbol Q
protect symbol R
protect symbol S
protect symbol largestIndex
protect symbol maxWt


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

-- used to compute tableau coefficient [Macdonald p.228]
I = (lam,mu) -> (
    lam' := conj lam;
    mu' := conj mu;
    mu' = appendZeros(mu',#lam'-#mu');
    
    theta' := for i from 0 to (#lam'-1) list (lam'#i-mu'#i);
    theta' = appendZeros(theta',1);
    
    if (number(theta',k -> k>=2)>0) then print("warning: theta=lam-mu is not a horizontal strip");
    ans := {};
    
    for i from 0 to #theta'-2 do (
        if (theta'#i > theta'#(i+1)) then (ans = append(ans,i+1))
        );
    ans
    )

-- used to compute tableau coefficient [Macdonald p.228]
phi = (lam,mu) -> (
    ind := I (lam,mu);
    ans := product for j from 0 to #ind-1 list (1-t^(number(lam,k -> k==ind#j)));
    ans
    )

-- tableau coefficient [Macdonald p.228]
phiT = T -> (
    seq := tabToPartSeq T;
    ans := product for i from 0 to #seq-2 list (phi (seq#(i+1),seq#i));
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

---------- Hall-Littlewood functions

-- returns the monomial x^T, where T is a tableau
TtoxT = T -> (
    product for entry in flatten tableauToList T list (
        if entry > 0 then (x_entry) else (1)
        )
    )

-- computes Q_{lam/mu} in the number of variables (at least #lam) [Macdonald p.229]
skewQ = (lam,mu,numVars) -> (
    if (lam != rsort lam or mu != rsort mu) then (
        error("skewQ error: lam, mu must be partitions");
        );
    if (unique lam == {0} or lam == {}) and (unique mu == {0} or mu == {}) then return 1;
    if #mu > #lam then return (0);
    for i from 0 to #mu-1 do (
        if lam#i < mu#i then return (0);
        );
    
    sum for T in genAllSSYT(lam,mu,numVars) list ((phiT T)*(TtoxT T))
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

-- computes Q_{lam} in the number of variables (at least #lam)
-- if lam is a composition, first reorder parts [Macdonald p.214]
Qlam = (lam,numVars) -> (
    if lam#-1 < 0 then return (0);
    
    Qreorder := (lam,numVars) -> (
        --print(lam);
        for i from 0 to #lam-2 do (
            if lam#i < lam#(i+1) then (
                lamSwitch := switch(i,i+1,lam);
                Rij := for k from 0 to #lam-1 list (
                    if k == i then (-1)
                    else if k == i+1 then (1)
                    else (0)
                    );
                r := lam#(i+1);
                s := lam#(i);
                
                if (r-s)%2 == 1 then (
                    m := (r-s-1)//2;
                    return(t*Qreorder(lamSwitch,numVars) + sum for k from 1 to m list ((t^(k+1)-t^(k-1))*Qreorder(lamSwitch + k*Rij,numVars)));
                    );
                m := (r-s)//2;
                return(t*Qreorder(lamSwitch,numVars) + ((t^m-t^(m-1))*Qreorder(lamSwitch+m*Rij,numVars)) + sum for k from 1 to m-1 list ((t^(k+1)-t^(k-1))*Qreorder(lamSwitch + k*Rij,numVars)));
                );
            );
        return Qlam(lam,numVars)
    );
    if lam != rsort lam then return (Qreorder(lam,numVars));
    
    skewQ(lam,{},numVars)
    )

-- returns x^lam
xLam = lam -> (
    if #lam == 0 then return 1;
    product for i from 1 to #lam list x_i^(lam#(i-1))
    )

-- converts lam to the variable Q_lam (for #lam <= 3)
lamToQ = lam -> (
    if lam != rsort lam then print("lamToQ error: lam not a partition");
    newPart := delete(0,lam);
    if #newPart > 3 then print("lamToQ error: lam to long");
    if #newPart == 0 then return 1;
    if #newPart == 1 then return (Q_(newPart#0));
    if #newPart == 2 then return (Q_(newPart#0,newPart#1));
    if #newPart == 3 then return (Q_(newPart#0,newPart#1,newPart#2));
    )

-- computes R_{ij}^n(lam) (1<=i,j)
Rijn = (i,j,n,lam) -> (
    if i == j then return(lam);
    Rij := for k from 0 to #lam-1 list (
        if k == i-1 then (1)
        else if k == j-1 then (-1)
        else (0)
        );
    lam + n*Rij
    )

-- Iverson bracket: [P] = 1 if P is true, = 0 if P is false
iversonBracket = P -> (
    if P then return 1;
    return 0;
    )

-- returns list of (nu,numRij,numUnique,Rijs,coeff1,coeff2)
-- numRij = total number of raising operators applied
-- numUnique = number of unique raising operators applied
-- Rijs = operators acting on lam - mu
-- coeff1 = factor due to reordering
-- coeff2 = factor due to operators
decomposeSkewBasisParts = (lam,mu) -> (
    mu' := appendZeros(mu,#lam-#mu);
    skewShape := lam - mu';
    muWt := sum mu;
    
    ijList := flatten for i from 1 to #lam-1 list for j from i+1 to #lam list {(i,j),min(lam#i,mu'#(i-1))-mu'#(j-1)};
    print(ijList);
    print(skewShape);
    
    theCount := 2;
    
    ans := {(skewShape,sub(1,R),"c_1",0,0,"")};
    for ijTerm in ijList do (
        for theComp in ans do (
            for k from 1 to ijTerm#1 do (
                --print(ijTerm#0#0,ijTerm#0#1,k,theComp#0);
                -- if theComp#1+k > min(lam#1,mu'#0) then break;
                iCurr := ijTerm#0#0;
                newComp := Rijn(ijTerm#0#0,ijTerm#0#1,k,theComp#0);
                if newComp#(iCurr-1) > lam#(iCurr-1) then break;
                if theComp#3+k > muWt then break;
                if newComp#-1<0 then break;
                if k > 1 then (
                    ans = append(ans,(newComp,sub(1,R),concatenate("c_",toString(theCount)),theComp#3+k,theComp#4+1,concatenate("R_{",toString(ijTerm#0#0),",",toString(ijTerm#0#1),"}^",toString(k)," ",theComp#5)));
                    ) else (
                    ans = append(ans,(newComp,sub(1,R),concatenate("c_",toString(theCount)),theComp#3+k,theComp#4+1,concatenate("R_{",toString(ijTerm#0#0),",",toString(ijTerm#0#1),"}"," ",theComp#5)));
                    );
                theCount = theCount + 1;
                );
            );
        );
    
    -- reorders compositions into partitions
    ans2 := {};
    for thePart in ans do (
        if rsort thePart#0 == thePart#0 then (
            ans2 = append(ans2,thePart)
            ) else (
            reorderedList := reorderPart(thePart#0);
            for newPart in reorderedList do (
                ans2 = append(ans2,(newPart#0,thePart#1*newPart#1,thePart#2,thePart#3,thePart#4,thePart#5));
                );
            );
        );
    
    rsort ans2 --select(ans2,thePart -> thePart#0#-1 >= 0)
    )


-- 
decomposeComps = (lam,mu) -> (
    mu' := appendZeros(mu,#lam-#mu);
    skewShape := lam - mu';
    
    ijList := flatten for i from 1 to #lam-1 list for j from i+1 to #lam list {(i,j),min(lam#i,mu'#(i-1))-mu'#(j-1)};
    
    ans := {(skewShape,0)};
    for ijTerm in ijList do (
        for theComp in ans do (
            for k from 1 to ijTerm#1 do (
                --print(ijTerm#0#0,ijTerm#0#1,k,theComp#0);
                if theComp#1+k > min(lam#1,mu'#0) then break;
                ans = append(ans,(Rijn(ijTerm#0#0,ijTerm#0#1,k,theComp#0),theComp#1+k));
                );
            );
        );
    
    rsort for theComp in ans list (theComp#0,(1-t)^(theComp#1))
    )

-- decomposes Q_{lam/mu} as a linear combination of Q_nu
decomposeSkew = {doPrint => true} >> o -> (lam,mu) -> (
    if lam == rsort lam and lam#-1 >= 0 and lam == mu then return(sub(1,S));
    
    ans := {};
    numVars := #lam;
    currPolyn := skewQ(lam,mu,numVars);
    
    while currPolyn != 0 do (
        leadPart := delete(0,(listForm leadTerm currPolyn)#0#0);
        leadCoeff := leadCoefficient currPolyn;
        
        basisFunction := Qlam(leadPart,numVars);
        basisCoeff := leadCoefficient basisFunction;
        
        theCoeff := (sub(leadCoeff,R))//(sub(basisCoeff,R));
        ans = append(ans,(leadPart,theCoeff));
        
        currPolyn = currPolyn - theCoeff * (basisFunction);
        );
    
    ans = rsort ans;
    
    if o.doPrint then (
        -- prints decomposition into latex code
        print("\n");
        print(concatenate("Q_{("|toString(lam)|")/("|toString(mu)|")}&=",decompToTex(ans)));
        
        -- prints decomposition into m2 functions
        print("\n");
        print(decompToM2(ans,numVars));
        
        if #lam <= 3 then (
            return(decompToPretty(ans));
            );
        );
    
    ans
    )

-- returns decomp as string of LaTeX
decompToTex = (theDecomp) -> (
    replace("\\*","",replace("\\+$","",concatenate(for theTerm in theDecomp list (
                        if theTerm#1 != 1 then ("("|toString(theTerm#1)|")Q_{("|toString(theTerm#0)|")}+")
                        else ("Q_{("|toString(theTerm#0)|")}+")
                        ))))
    )

-- returns decomp as string of M2 code
decompToM2 = (theDecomp,num) -> (
    replace("\\+$","",concatenate(for theTerm in theDecomp list ("("|toString(theTerm#1)|")*Qlam("|toString(theTerm#0)|","|toString(num)|")+")))
    )

-- returns decomp as element of S
decompToPretty = theDecomp -> (
    sum for theTerm in theDecomp list (sub(theTerm#1,S) * (lamToQ(theTerm#0)))
    )

--------------- conjectures

-- computes Q_lam/mu using raising operator conjecture, where ell(mu)=1
skewFormula1 = (lam,mu,numVars) -> (
    if #mu != 1 then (
        print("skewFormula1 error: wrong input");
        return(0);
        );
    if #lam == 1 then (
        lam = appendZeros(lam,1);
        );
    
    theList := flatten for deg from 0 to mu#0 list (
        for theComp in compositions(#lam-1,deg) list (
            (number(theComp,i -> i >= 1)-iversonBracket(0 < deg and deg == mu#0),lam + prepend(deg-mu#0,-theComp))
            )
        );
    
    -- print(theList);
    sum for theTerm in theList list ((1-t)^(theTerm#0)*Qlam(theTerm#1,numVars))
    )

-- computes Q_lam/mu using raising operator conjecture, where ell(lam)=ell(mu)=2
skewFormula2 = (lam,mu,numVars) -> (
    if #lam != 2 and #mu != 2 then (
        print("skewFormula2 error: wrong input");
        return(0);
        );
    
    skewShape := lam - mu;
    
    termList := for i from 0 to mu#0-mu#1 list (Rijn(1,2,i,skewShape),(1-t)^(iversonBracket(0 < i and i < mu#0-mu#1)));
    
    sum for theTerm in termList list ((Qlam(theTerm#0,numVars))*(theTerm#1))
    --rsort termList
    )

ijListToRij = (theList,muLen,lamLen) -> (
    for k from 1 to lamLen list (
        if (any(theList, n -> n == k) and k <= muLen) then (1)
        else if (any(theList, n -> n == k) and k > muLen) then (-1)
        else (0)
        )
    )

-- computes Q_lam/mu using raising operator conjecture, where mu=1^m
skewFormula3 = (lam,mu,numVars) -> (
    if (max mu != 1) or (min mu != 1) then (
        print("skewFormula3 error: wrong input");
        return(0);
        );
    
    skewShape := lam - appendZeros(mu,#lam-#mu);
    
    iList := set(1..(#mu));
    jList := set((#mu+1)..(#lam));
    
    
    ijList := {{}};
    for k from 1 to min(#mu,#lam-#mu) do (
        for thei in subsets(iList,k) do (
            for thej in subsets(jList,k) do (
                ijList = append(ijList,sort toList(thei+thej));
                );
            );
        );
    -- print(ijList);
    
    ijListToRij2 := (theList,muLen,lamLen) -> (
        for k from 1 to lamLen list (
            if (any(theList, n -> n == k) and k <= muLen) then (1)
            else if (any(theList, n -> n == k) and k > muLen) then (-1)
            else (0)
            )
        );
    
    sum for theList in ijList list (
        Qlam(skewShape + ijListToRij2(theList,#mu,#lam),#lam)
        )
    )

-- computes Q_lam/mu using raising operator conjecture, where lam=k^m, mu=(2,1)
skewFormula4 = (lam,mu,numVars) -> (
    if (max lam != min lam) or (mu != {2,1}) then (
        print("skewFormula4 error: wrong input");
        return(0);
        );
    
    k := lam#0;
    m := #lam;
    
    theCoeff := sum for i from 1 to m-1 list (i*(t^(i-1)+t^(2*(m-1)-i)));
    
    thePart := toList((m-2):k);
    thePart = append(thePart,k-1);
    thePart = append(thePart,k-2);
    
    theCoeff*Qlam(thePart,numVars)
    )
