// Root certificate audit, authored separately from returned implementations.
// Head windows: sliding prefix minimum on two periods, not Kadane sums.
// Integer tails: occurrence-rank arithmetic, not full-word colour expansion.
// Coverage: enumerate sorted period multisets and delete matched routes.
// Also checks the independent multiple-head foundation whole-signature two-group classifications.
#include <algorithm>
#include <array>
#include <cstdint>
#include <deque>
#include <fstream>
#include <iostream>
#include <numeric>
#include <sstream>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

using I = std::int64_t;
using U = std::uint64_t;
using Z = __int128_t;
void need(bool b, const std::string& what) { if (!b) throw std::runtime_error(what); }
Z absz(Z x) { return x < 0 ? -x : x; }
Z gcdz(Z a,Z b) { a=absz(a);b=absz(b);while(b){Z t=a%b;a=b;b=t;}return a; }
struct Q {
    Z n,d;
    Q(Z a=0,Z b=1):n(a),d(b) { need(d!=0,"zero denominator");if(d<0){n=-n;d=-d;}Z g=gcdz(n,d);n/=g;d/=g; }
};
Q operator+(Q a,Q b){return Q(a.n*b.d+b.n*a.d,a.d*b.d);}
Q operator-(Q a,Q b){return Q(a.n*b.d-b.n*a.d,a.d*b.d);}
Q operator*(Q a,Q b){return Q(a.n*b.n,a.d*b.d);}
Q operator/(Q a,Q b){return Q(a.n*b.d,a.d*b.n);}
bool operator<(Q a,Q b){return a.n*b.d<b.n*a.d;}
bool operator==(Q a,Q b){return a.n==b.n&&a.d==b.d;}
bool operator<=(Q a,Q b){return !(b<a);}
Q qmax(Q a,Q b){return a<b?b:a;}

I K=2; std::array<U,11> powers;
struct Word { std::string text; std::uint32_t symbols=0; };
struct Face { I alpha, deficit, period; std::vector<int> gaps; };
std::vector<Word> words;
std::vector<Face> faces;
std::unordered_map<U,std::size_t> routes;
std::unordered_set<U> residual;
std::array<U,18> by_q{};
std::array<U,8> multi{},two_groups{};
U syntax=0,matched=0,rank_checks=0,window_checks=0,endpoint_only=0;
I max_base=0,max_period=0,max_density=0;

bool two_group_proof(int p,const std::vector<int>& c,I upper) {
    int n=p+int(c.size());
    Q lo=qmax(Q(1,11),Q(1,n)),hi=Q(upper,K)-Q(p-1,11);
    for(int j=p;j<n;++j)lo=qmax(lo,(Q(1)-Q(n-j,c[j-p]))/Q(j));
    if(hi<lo)return true;
    std::vector<Q> boundaries{lo,hi};
    for(int j=1;j<p;++j){Q t=Q(11-n+j,11*j);if(lo<t&&t<hi)boundaries.push_back(t);}
    std::sort(boundaries.begin(),boundaries.end());
    boundaries.erase(std::unique(boundaries.begin(),boundaries.end()),boundaries.end());
    auto f=[&](Q t){Q sum=t;for(int j=1;j<p;++j)sum=sum+qmax(Q(1,11),(Q(1)-Q(j)*t)/Q(n-j));return sum;};
    if(boundaries.size()==1)return Q(upper,K)<=f(lo);
    // On each segment the active branches are fixed. Verify its affine
    // value at both endpoints, including equality against the strict guard.
    for(std::size_t i=1;i<boundaries.size();++i){
        Q left=boundaries[i-1],right=boundaries[i],mid=(left+right)/Q(2);
        Q slope(1),offset(0);
        for(int j=1;j<p;++j){
            if(Q(1,11)<(Q(1)-Q(j)*mid)/Q(n-j)){
                slope=slope-Q(j,n-j);offset=offset+Q(1,n-j);
            }else offset=offset+Q(1,11);
        }
        for(Q t:{left,right}){
            Q value=slope*t+offset;
            need(value==f(t),"affine branch mismatch");
            if(value<Q(upper,K))return false;
        }
    }
    return true;
}

void enumerate(std::vector<int>& c,int least_next,I discount,I actual,U code) {
    int q=int(c.size());
    if(q){
        ++syntax;
        I gamma=c.back()==21?K/22:K/(2*(c.front()+1));
        I upper=5*(K/6)+gamma-discount;
        if(upper>K/11){
            auto it=routes.find(code);need(it!=routes.end(),"missing one-head signature");
            const Face& f=faces[it->second];need(int(f.gaps.size())==q,"wrong tail count");
            need(upper<=f.alpha,"head cap insufficient");
            for(int j=0;j<q;++j)need(f.gaps[j]<=c[j],"integer child gap exceeds period");
            if(upper==f.alpha&&f.deficit==K)++endpoint_only;
            routes.erase(it);++matched;++by_q[q];max_density=std::max(max_density,upper+actual);
            for(int p=2;p<=7&&2*p+q<=19;++p){
                if(upper<=p*(K/11))continue;
                ++multi[p];U key=(code<<3)|U(p);
                if(residual.erase(key)==0){need(two_group_proof(p,c,upper),"false whole-signature closure");++two_groups[p];}
                else need(!two_group_proof(p,c,upper),"false residual signature");
            }
        }
    }
    if(q==17)return;
    for(int d=least_next;d<=21;++d){
        c.push_back(d);
        enumerate(c,d,discount+K/(d+1),actual+K/d,code+powers[d-11]);
        c.pop_back();
    }
}

int main(int argc,char**argv){try{
    need(argc==5,"usage: words.tsv faces.tsv routes.tsv residual.csv");
    I l=1;for(I d=1;d<=22;++d)l=std::lcm(l,d);K=2*l;
    need(K==465585120,"grid mismatch");powers[0]=1;for(int j=1;j<11;++j)powers[j]=18*powers[j-1];
    {
        std::ifstream in(argv[1]);need(bool(in),"word file");std::string line;
        while(std::getline(in,line)){
            std::istringstream s(line);std::size_t id;std::string name,w,extra;
            need(bool(s>>id>>name>>w)&&!(s>>extra),"word syntax");need(id==words.size()&&!w.empty(),"word id");
            Word row{w,0};for(char x:w){need(x>='A'&&x<='Z',"word symbol");row.symbols|=std::uint32_t(1)<<(x-'A');}
            max_base=std::max(max_base,I(w.size()));words.push_back(std::move(row));
        }
    }
    {
        std::ifstream in(argv[2]);need(bool(in),"face file");std::string line;
        while(std::getline(in,line)){
            std::istringstream s(line);std::size_t id,wi;I alpha;int groups;
            need(bool(s>>id>>wi>>alpha>>groups),"face syntax");
            need(id==faces.size()&&wi<words.size()&&alpha>=0&&alpha<=K&&groups>0&&groups<=17,"face fields");
            const Word& w=words[wi];int P=int(w.text.size());
            std::vector<std::vector<int>> positions(groups);std::vector<int> multiplicities;
            std::uint32_t used=0;int q=0;
            for(int g=0;g<groups;++g){
                std::string spec;need(bool(s>>spec),"missing group");auto sep=spec.find(':');need(sep!=std::string::npos,"group syntax");
                U mask=std::stoull(spec.substr(0,sep));int m=std::stoi(spec.substr(sep+1));
                need(mask>0&&(mask&~U(w.symbols))==0&&(mask&used)==0&&m>0&&m<=17,"invalid group");
                used|=std::uint32_t(mask);q+=m;multiplicities.push_back(m);
                for(int t=0;t<P;++t)if(mask&(U(1)<<(w.text[t]-'A')))positions[g].push_back(t);
                need(!positions[g].empty(),"empty group");
            }
            std::string extra;need(!(s>>extra)&&q>0&&q<=17,"face trailing/count");
            std::vector<I> prefix(2*P+1,0);
            for(int t=0;t<2*P;++t){bool head=(used&(std::uint32_t(1)<<(w.text[t%P]-'A')))==0;prefix[t+1]=prefix[t]+alpha-(head?K:0);}
            need(prefix[P]<=0,"head drift");
            std::deque<int> minima;I deficit=0;
            for(int right=1;right<=2*P;++right){
                int start=right-1;
                if(start<P){while(!minima.empty()&&prefix[minima.back()]>=prefix[start])minima.pop_back();minima.push_back(start);}
                while(!minima.empty()&&minima.front()<right-P)minima.pop_front();
                if(!minima.empty()){deficit=std::max(deficit,prefix[right]-prefix[minima.front()]);++window_checks;}
            }
            need(deficit<=K,"head window deficit");
            std::vector<int> gaps;I lift=1;
            for(int g=0;g<groups;++g){
                const auto& pos=positions[g];int r=int(pos.size()),m=multiplicities[g],div=std::gcd(r,m);
                lift=std::lcm(lift,I(m/div));
                auto time_at=[&](int k){return I(k/r)*P+pos[k%r];};
                for(int child=0;child<m;++child){
                    I worst=0;
                    for(int step=0;step<r/div;++step){int k=child+step*m;worst=std::max(worst,time_at(k+m)-time_at(k));++rank_checks;}
                    need(worst>0&&worst<=21,"tail rank gap");gaps.push_back(std::max(11,int(worst)));
                }
            }
            std::sort(gaps.begin(),gaps.end());I period=I(P)*lift;need(period<=28914,"claimed period bound");max_period=std::max(max_period,period);
            faces.push_back({alpha,deficit,period,std::move(gaps)});
        }
    }
    {
        std::ifstream in(argv[3]);need(bool(in),"routes file");U code;std::size_t id;routes.reserve(2200000);
        while(in>>code>>id){need(id<faces.size(),"route face");need(routes.emplace(code,id).second,"duplicate route");}
        need(in.eof(),"route syntax");
    }
    {
        std::ifstream in(argv[4]);need(bool(in),"multiple-head foundation residual file");std::string line;residual.reserve(1200000);
        while(std::getline(in,line)){
            std::replace(line.begin(),line.end(),',',' ');std::istringstream s(line);int p,d,prev=11,q=0;U code=0;
            need(bool(s>>p)&&p>=2&&p<=7,"residual p");
            while(s>>d){need(d>=prev&&d<=21,"residual signature");code+=powers[d-11];prev=d;++q;}
            need(s.eof()&&q>0&&2*p+q<=19,"residual syntax/count");
            need(residual.insert((code<<3)|U(p)).second,"duplicate residual");
        }
    }
    std::vector<int> c;enumerate(c,11,0,0,0);
    need(routes.empty()&&residual.empty(),"extra route or residual signature");
    need(matched==2117841&&syntax==21474179,"one-head reported count mismatch");
    need(words.size()==11058&&faces.size()==68160,"proof inventory mismatch");
    need(max_period==28914&&endpoint_only==5,"period/endpoint summary mismatch");
    std::cout<<"{\n  \"outcome\": \"VERIFIED\",\n  \"r063_words\": "<<words.size()<<",\n  \"r063_templates\": "<<faces.size()<<",\n  \"r063_routes\": "<<matched<<",\n  \"syntactic_signatures\": "<<syntax<<",\n  \"head_prefix_checks\": "<<window_checks<<",\n  \"tail_rank_checks\": "<<rank_checks<<",\n  \"maximum_base_period\": "<<max_base<<",\n  \"maximum_expanded_period\": "<<max_period<<",\n  \"open_endpoint_only_routes\": "<<endpoint_only<<",\n  \"maximum_boundary_density\": \""<<max_density/std::gcd(max_density,K)<<'/'<<K/std::gcd(max_density,K)<<"\",\n  \"r063_by_tail_count\": [";
    for(int q=1;q<=17;++q)std::cout<<(q>1?", ":"")<<by_q[q];
    std::cout<<"],\n  \"r064_admissible_by_heads\": [";
    for(int p=2;p<=7;++p)std::cout<<(p>2?", ":"")<<multi[p];
    std::cout<<"],\n  \"r064_two_group_closures_by_heads\": [";
    for(int p=2;p<=7;++p)std::cout<<(p>2?", ":"")<<two_groups[p];
    std::cout<<"],\n  \"missing_or_extra_signatures\": 0\n}\n";
    return 0;
}catch(const std::exception& e){std::cerr<<"ROOT CHECK FAILED: "<<e.what()<<'\n';return 1;}}
