#!/usr/bin/env python3
"""Root check of the original multiple-head foundation ZIP's real-region certificates.

No returned modules are imported. Literal caps use occurrence-rank spans;
envelope leaves use affine-segment inequalities; signatures use multiplicities.
"""
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path
import gzip
import hashlib
import io
import json
import platform
import time
import zipfile

ROOT = Path(__file__).resolve().parents[1]
ARCHIVE = ROOT / 'data/multiple-head-foundation.zip'
Z = zipfile.ZipFile(ARCHIVE)
PREFIX = ''


def read(name):
    data = Z.read(PREFIX+name)
    if name.endswith('.gz'):
        data = gzip.decompress(data)
    return json.loads(data)


base_rows = read('calendars.json')
words = {}
extras = ['gap_p7_calendars.json', 'sample_verified_calendars.json',
          'gap_p7_aug1_calendars.json', 'gap_p7_aug2_calendars.json',
          'gap_p6_aug3_calendars.json', 'gap_p6_aug4_calendars.json',
          'three_stream_samples.json', 'analytic_calendars.json']
for row in base_rows + [row for name in extras for row in read('outputs/'+name)]:
    key = row['id']
    if key in words:
        assert all(words[key][field] == row[field] for field in ['word', 'period', 'caps']), key
    words[key] = row

rank_comparisons = 0


@lru_cache(None)
def caps(key):
    global rank_comparisons
    row = words[key]
    word = row['word']
    period = len(word)
    assert period == row['period'] and period > 0
    result = []
    for symbol in sorted(set(word)):
        positions = [t for t, a in enumerate(word) if a == symbol]
        count = len(positions)
        best_n, best_d, closed = count, period, True
        twice = positions + [t+period for t in positions]
        for rank in range(1, count+1):
            distance = max(twice[start+rank]-twice[start] for start in range(count))
            rank_comparisons += count
            if distance <= 1:
                continue
            denominator = distance-1
            left, right = rank*best_d, best_n*denominator
            if left < right:
                best_n, best_d, closed = rank, denominator, False
            elif left == right:
                closed = False
        result.append((F(best_n,best_d), closed))
    assert result == [(F(c['rate']),c['closed']) for c in row['caps']], key
    return tuple(result)


@lru_cache(None)
def expansion(key, sizes):
    source = caps(key)
    assert len(source) == len(sizes)
    result = []
    for (rate, closed), m in zip(source, sizes):
        assert type(m) is int and m >= 0
        if m:
            result.extend([(rate/m, closed)]*m)
    return tuple(sorted(result, reverse=True))


def upper(c):
    return F(5,6) + (F(1,22) if 21 in c else F(1,2*(min(c)+1))) - sum((F(1,x+1) for x in c),F())


def domain(p, max_q):
    result = set()
    def visit(d, remaining, c):
        if d == 22:
            if c and F(p,11) < upper(c):
                result.add(c)
            return
        for multiplicity in range(remaining+1):
            visit(d+1, remaining-multiplicity, c+(d,)*multiplicity)
    visit(11, max_q, ())
    return result


def affine_envelope(p, c, limit, lower):
    n = p+len(c)
    left = max([lower[0],F(1,n)] + [(1-F(n-j,c[j-p]))/j for j in range(p,n)])
    right = limit-sum(lower[1:])
    if left > right:
        return 0
    splits = sorted({left,right} | {t for j in range(1,p)
                    if left <= (t := (1-(n-j)*lower[j])/j) <= right})
    def value(t):
        return t+sum(max(lower[j],(1-j*t)/(n-j)) for j in range(1,p))
    if len(splits) == 1:
        assert value(left) >= limit
        return 1
    checks = 0
    for a,b in zip(splits,splits[1:]):
        midpoint=(a+b)/2
        slope, intercept = F(1),F()
        for j in range(1,p):
            if (1-j*midpoint)/(n-j) > lower[j]:
                slope -= F(j,n-j)
                intercept += F(1,n-j)
            else:
                intercept += lower[j]
        for endpoint in (a,b):
            v=slope*endpoint+intercept
            assert v == value(endpoint) and v >= limit
            checks += 1
    return checks


def verify(p, tag, max_q):
    certificates=read(f'outputs/cover_p{p}{tag}_certificates.json.gz')
    admitted=domain(p,max_q)
    present={tuple(map(int,key.split(','))) for key in certificates}
    assert present <= admitted and len(present) == len(certificates)
    methods, assignments, used = Counter(),set(),set()
    nodes_checked=0
    affine_checks=0
    maximum_depth=0
    for c in sorted(present):
        proof=certificates[','.join(map(str,c))]
        U=upper(c)
        assert F(proof['U']) == U
        nodes=proof['nodes']
        done, active = {},set()
        def visit(index, expected_l, expected_s):
            nonlocal affine_checks
            assert type(index) is int and 0<=index<len(nodes)
            node=nodes[index]
            lower=tuple(map(F,node['lower']))
            strict=tuple(node['strict'])
            assert len(lower)==len(strict)==p
            assert all(type(x) is bool for x in strict)
            assert (lower,strict)==(expected_l,expected_s)
            assert all(lower[j]>=lower[j+1] for j in range(p-1)) and lower[-1]>=F(1,11)
            if index in done:
                return done[index]
            assert index not in active,'cyclic graph'
            active.add(index)
            kind=node['kind'];methods[kind]+=1
            height=1
            if kind=='sum':
                assert sum(lower)>=U
            elif kind in ['envelope','empty_interval']:
                affine_checks+=affine_envelope(p,c,U,lower)
            else:
                assert kind=='box',kind
                key=node['word'];sizes=tuple(node['sizes'])
                bounds=expansion(key,sizes)
                assert len(bounds)==p+len(c)
                for d,(cap,closed) in zip(c,bounds[p:]):
                    assert F(1,d)<cap or (F(1,d)==cap and closed)
                used.add(key);assignments.add((key,sizes))
                children=dict(node['children'])
                assert len(children)==len(node['children']) and set(children)<=set(range(p))
                for i,(cap,closed) in enumerate(bounds[:p]):
                    if i not in children:
                        least_sum=sum(max(x,cap) for x in lower[:i+1])+sum(lower[i+1:])
                        assert least_sum>=U
                        continue
                    ll,ss=list(lower),list(strict)
                    if cap>ll[i]:ll[i],ss[i]=cap,closed
                    elif cap==ll[i]:ss[i]=ss[i] or closed
                    for j in range(p-2,-1,-1):
                        if ll[j]<ll[j+1]:ll[j],ss[j]=ll[j+1],ss[j+1]
                        elif ll[j]==ll[j+1]:ss[j]=ss[j] or ss[j+1]
                    height=max(height,1+visit(children[i],tuple(ll),tuple(ss)))
            active.remove(index);done[index]=height
            return height
        maximum_depth=max(maximum_depth,visit(0,(F(1,11),)*p,(False,)*p))
        assert len(done)==len(nodes)
        nodes_checked+=len(nodes)
    result={'heads':p,'maximum_tail_count_in_scope':max_q,'admissible_signatures':len(admitted),
            'covered_signatures':len(present),'proof_nodes':nodes_checked,'node_kinds':dict(methods),
            'affine_endpoint_checks':affine_checks,'words_used':len(used),'assignments':len(assignments),
            'maximum_graph_height':maximum_depth,'maximum_literal_period':max(words[key]['period'] for key in used),
            'remaining_signatures':[list(c) for c in sorted(admitted-present)]}
    archived=read(f'outputs/verified_cover_p{p}{tag}.json')
    for ours,theirs in [('covered_signatures','certified_signatures'),('proof_nodes','nodes'),
                       ('words_used','unique_words_used'),('assignments','grouped_assignments_used'),
                       ('remaining_signatures','missing_signatures')]:
        assert result[ours]==archived[theirs],(ours,result[ours],archived[theirs])
    print(json.dumps({k:v for k,v in result.items() if k!='remaining_signatures'}),flush=True)
    return result


if __name__=='__main__':
    started=time.monotonic()
    results=[verify(7,'_aug3',5),verify(6,'_aug5',7),verify(2,'_q1',1)]
    assert [r['covered_signatures'] for r in results]==[780,4757,11]
    assert [r['proof_nodes'] for r in results]==[4589,42858,52]
    # Independently recalculate the five words in the analytic two-head proof.
    analytic=[('1212132112',[(F(1,2),False),(F(2,5),False),(F(1,10),True)]),
              ('213121211',[(F(5,9),True),(F(1,3),False),(F(1,9),True)]),
              ('1211211213',[(F(3,5),False),(F(3,10),True),(F(1,10),True)]),
              ('121112113',[(F(2,3),False),(F(2,9),True),(F(1,9),True)]),
              ('12111211121112113',[(F(2,3),False),(F(4,17),True),(F(1,17),True)])]
    for i,(word,expected) in enumerate(analytic):
        key=f'root-analytic-{i}'
        words[key]={'word':word,'period':len(word),'caps':[{'rate':str(q),'closed':cl} for q,cl in expected]}
        assert caps(key)==tuple(expected)
    result={'outcome':'VERIFIED','python':platform.python_version(),'seconds':time.monotonic()-started,
            'archive_sha256':hashlib.sha256(ARCHIVE.read_bytes()).hexdigest(),
            'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'coverage':results,'rank_comparisons':rank_comparisons,'analytic_calendars':len(analytic),
            'scope':'Original ZIP certificates; no returned implementation imported; no discovery search or Lean check.'}
    print(json.dumps(result, sort_keys=True))
