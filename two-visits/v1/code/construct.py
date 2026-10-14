"""Construct finite 2-Visits at D <= 1+1/(n(n-1)).

The infeasible inputs in this range are relabellings of (n-1,n,...,n), n>=2.
The algorithm repairs anchor-cluster matchings with an auxiliary calendar;
see Sections 7.2 and 8-10 of the accompanying article.
Uses the Python standard library.
"""
from fractions import Fraction
from itertools import groupby
from typing import Iterable, Any


class CriticalInfeasible(ValueError):
    """An infeasible instance in the critical family B_n."""


def density(values: list[int]) -> Fraction:
    return sum((Fraction(1, d) for d in values), Fraction())


def threshold(n: int) -> Fraction:
    if n < 2:
        raise ValueError('The finite minimum-infeasible formula requires n >= 2')
    return 1 + Fraction(1, n*(n-1))


def verify(values: list[int], word: list[int]) -> None:
    if len(word) != 2*len(values):
        raise AssertionError('Wrong word length')
    first = [-1]*len(values)
    counts = [0]*len(values)
    for position, label in enumerate(word, start=1):
        if type(label) is not int or not 0 <= label < len(values):
            raise AssertionError('Invalid label')
        counts[label] += 1
        if counts[label] == 1:
            first[label] = position
            if position > values[label]:
                raise AssertionError(('Initial deadline', label, position))
        elif counts[label] == 2:
            if position-first[label] > values[label]:
                raise AssertionError(('Successive gap', label, first[label], position))
        else:
            raise AssertionError(('Excess multiplicity', label))
    if any(c != 2 for c in counts):
        raise AssertionError('Wrong multiplicity')


def schedule(values: Iterable[int], trace: list[dict[str,Any]] | None=None) -> list[int]:
    original=list(values);N=len(original)
    if any(type(d) is not int or d<1 for d in original):
        raise ValueError('Positive integer deadlines required')
    if N<=1:
        return [] if N==0 else [0,0]
    D=density(original)
    if D>threshold(N):
        raise ValueError('Density is outside the fixed-count promise; no infeasibility conclusion')
    records=sorted((d,i) for i,d in enumerate(original))
    if [d for d,_ in records]==[N-1]+[N]*(N-1):
        raise CriticalInfeasible('Forced total gap n^2 exceeds deadline sum n^2-1')
    removed=[]
    while records and records[-1][0]>=2*len(records)-1:
        removed.append(records.pop())
    n=len(records);d=[0]+[v for v,_ in records];names=[-1]+[i for _,i in records]
    a=[0]*(n+1);suffix_min=2*n
    for i in range(n,0,-1):
        suffix_min=min(suffix_min,d[i]-i);a[i]=i+suffix_min
        assert i<=a[i]<=d[i]
    occupied=set(a[1:]);v=[0]+[i for i in range(1,2*n+1) if i not in occupied]
    assert len(v)==n+1
    word=[None]*(2*n)
    def put(position:int,index:int)->None:
        assert 1<=position<=2*n and word[position-1] is None
        word[position-1]=names[index]
    for H,iterator in groupby(range(1,n+1),key=lambda i:a[i]-i):
        indices=list(iterator);p,q=indices[0]-1,indices[-1]
        if all(v[i]<=a[i]+d[i] for i in indices):
            for i in indices:put(a[i],i);put(v[i],i)
            if trace is not None:trace.append({'kind':'sorted','p':p,'q':q})
            continue
        T=v[q];t=T-2*q;M=q+t
        assert t>=0 and q<=M<=n
        c=2*H-t;K=q-H+t
        assert c>=1 and H>p
        R=q-1
        while d[R]>=K:R-=1
        assert R>H
        short=list(range(H+1,R+1));long=list(range(R+1,q+1))
        widths=[K-d[i] for i in short];capacity=[d[i]-K for i in long]
        assert short and long and capacity[-1]==c and min(capacity)>=0
        starts=[];ends=[];s=0;finished=0;candidates=0
        for j,width in enumerate(widths,start=1):
            s=max(s,(ends[-1] if ends else 0)-width)
            while True:
                while finished<len(ends) and ends[finished]<=s:finished+=1
                cap=capacity[s] if s<len(capacity) else c
                candidates+=1
                if len(ends)-finished+1<=cap:break
                s+=1
            end=s+width;starts.append(s);ends.append(end)
            assert end<=K-width-2*H-j
        assert ends[-1]<len(long)
        def permutation(cuts:list[int])->list[int]:
            result=[];next_short=0
            for cut in range(len(long)+1):
                while next_short<len(short) and cuts[next_short]==cut:
                    result.append(short[next_short]);next_short+=1
                if cut<len(long):result.append(long[cut])
            assert next_short==len(short)
            return result
        for i in range(p+1,H+1):put(a[i],i);put(v[i],i)
        for rank,i in enumerate(permutation(ends),start=1):put(2*H+rank,i)
        for rank,i in enumerate(permutation(starts),start=1):put(v[H+rank],i)
        if trace is not None:
            trace.append({'kind':'sweep','p':p,'q':q,'M':M,'H':H,'t':t,'c':c,'K':K,
                          'widths':widths,'capacities':capacity,'starts':starts,'ends':ends,
                          'candidates':candidates})
    assert all(label is not None for label in word)
    result=[int(label) for label in word]
    for _,label in reversed(removed):result.extend((label,label))
    verify(original,result)
    return result


if __name__=='__main__':
    import argparse,json
    from pathlib import Path
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('deadlines',nargs='*',type=int)
    parser.add_argument('--input',type=Path)
    parser.add_argument('--trace',action='store_true')
    args=parser.parse_args()
    if args.input and args.deadlines:parser.error('Use positional deadlines or --input, not both')
    try:
        ds=json.loads(args.input.read_text()) if args.input else args.deadlines
        if not isinstance(ds,list):raise ValueError('JSON input must be an array')
        details=[] if args.trace else None
        answer=schedule(ds,details)
        out={'deadlines':ds,'status':'feasible','word':answer}
        if details is not None:out['clusters']=details
    except CriticalInfeasible as exc:
        N=len(ds)
        out={'deadlines':ds,'status':'infeasible','certificate':{'family':'B_n','n':N,
             'forced_total_gap':N*N,'deadline_sum':N*N-1,'density':str(threshold(N))}}
    except (ValueError,OSError,AssertionError) as exc:
        parser.exit(2,f'Failed: {exc}\n')
    print(json.dumps(out,indent=2))
