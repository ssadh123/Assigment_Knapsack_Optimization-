#include <iostream>
#include <vector>
#include <tuple>
#include <climits>
#include <cmath>
using namespace std;
// Name: Saumya Sadh
// PID: A17043544

//QUESTION 1 
tuple<vector<vector<int>>, vector<int>, int> myBranchBound(vector<vector<int>> C)
{
    int n = (int)C.size();
    vector<vector<int>> X(n, vector<int>(n, 0));
    vector<int> ub_list;
    int node_count = 0;
    if (n == 0) return make_tuple(X, ub_list, node_count);

    auto SNH_global = [&](const vector<vector<int>>& A){
        vector<int> r(n,0), c(n,0), a(n,-1);
        long long cost = 0;
        for (int k=0;k<n;++k){
            int br=-1, bc=-1, bv=INT_MAX;
            for (int i=0;i<n;++i) if(!r[i]){
                for (int j=0;j<n;++j) if(!c[j]){
                    if (A[i][j] < bv){ bv=A[i][j]; br=i; bc=j; }
                }
            }
            if (br==-1 || bc==-1 || bv==INT_MAX) return pair<int,vector<int>>(INT_MAX, vector<int>(n,-1));
            r[br]=1; c[bc]=1; a[br]=bc; cost+=bv;
            if (cost>INT_MAX) return pair<int,vector<int>>(INT_MAX, vector<int>(n,-1));
        }
        return pair<int,vector<int>>((int)cost, a);
    };

    auto rowMinLB = [&](const vector<vector<int>>& A, const vector<int>& assign){
        vector<int> colUsed(n,0);
        long long s = 0;
        for (int i=0;i<n;++i){
            if (assign[i]!=-1){
                s += A[i][assign[i]];
                if (assign[i]>=0 && assign[i]<n) colUsed[assign[i]]=1;
            }
        }
        for (int i=0;i<n;++i) if(assign[i]==-1){
            int best = INT_MAX;
            for (int j=0;j<n;++j) if(!colUsed[j]){
                if (A[i][j] < best) best = A[i][j];
            }
            if (best==INT_MAX) return INT_MAX;
            s += best;
            if (s>INT_MAX) return INT_MAX;
        }
        return (int)s;
    };

    auto greedyUB_from_partial = [&](const vector<vector<int>>& A, const vector<int>& assign){
        int n = (int)A.size();
        vector<int> r(n,0), c(n,0), a = assign;
        long long cost = 0;
        for (int i=0;i<n;++i){
            if (a[i]!=-1){
                r[i]=1;
                if (a[i]>=0 && a[i]<n) c[a[i]]=1;
                cost += A[i][a[i]];
                if (cost>INT_MAX) return pair<int,vector<int>>(INT_MAX, vector<int>(n,-1));
            }
        }
        for (int k=0;k<n;++k){
            int br=-1, bc=-1, bv=INT_MAX;
            for (int i=0;i<n;++i) if(!r[i]){
                for (int j=0;j<n;++j) if(!c[j]){
                    if (A[i][j] < bv){ bv=A[i][j]; br=i; bc=j; }
                }
            }
            if (br==-1) break;
            if (bc==-1 || bv==INT_MAX) return pair<int,vector<int>>(INT_MAX, vector<int>(n,-1));
            r[br]=1; c[bc]=1; a[br]=bc; cost+=bv;
            if (cost>INT_MAX) return pair<int,vector<int>>(INT_MAX, vector<int>(n,-1));
        }
        for (int i=0;i<n;++i) if (a[i]==-1) return pair<int,vector<int>>(INT_MAX, vector<int>(n,-1));
        return pair<int,vector<int>>((int)cost, a);
    };

    vector<int> bestAssign(n,-1);
    vector<int> initAssign;
    int bestUB;
    { auto tmp = SNH_global(C); bestUB = tmp.first; initAssign = tmp.second; }
    if (bestUB==INT_MAX) ub_list.push_back(INT_MAX);
    else {
        ub_list.push_back(bestUB);
        bestAssign = initAssign;
        for (int i=0;i<n;++i) if (initAssign[i]>=0) X[i][initAssign[i]]=1;
    }

    struct Node{ vector<int> assign; int lb; };

  
    vector<Node> open;
    Node root; root.assign.assign(n,-1);
    root.lb = rowMinLB(C, root.assign);
    ++node_count; 
    open.push_back(root);

    while (!open.empty()) {
        // pick best
        int best_i = 0;
        for (int i = 1; i < (int)open.size(); ++i)
            if (open[i].lb < open[best_i].lb) best_i = i;
    
        // take it out efficiently (and avoid copies)
        Node cur = std::move(open[best_i]);
        if (best_i != (int)open.size() - 1) {
            open[best_i] = std::move(open.back());
        }
        open.pop_back();
    
        // count an expansion *here*
        ++node_count;
    
        // optional: prune right after popping (don’t branch a dominated node)
        if (cur.lb > bestUB) continue;
    
        // try UB from this partial
        {
            auto ub_try = greedyUB_from_partial(C, cur.assign);
            int ub_val = ub_try.first;
            if (ub_val < bestUB) {
                bestUB = ub_val;
                bestAssign = ub_try.second;
                ub_list.push_back(bestUB);  // records only strict improvements
            }
        }
    
        // find next free row
        int r = -1; for (int i = 0; i < n; ++i) if (cur.assign[i] == -1) { r = i; break; }
        if (r == -1) continue; // complete assignment reached
    
        // branch on feasible columns
        vector<int> colUsed(n, 0);
        for (int i = 0; i < n; ++i) if (cur.assign[i] != -1) colUsed[cur.assign[i]] = 1;
    
        for (int j = 0; j < n; ++j) {
            if (colUsed[j]) continue;
            if (C[r][j] == INT_MAX) continue;
    
            Node child = cur;                  // copy is fine; assign is small
            child.assign[r] = j;
            child.lb = rowMinLB(C, child.assign);
    
            // (don’t increment node_count here!)
            // optional: only try UB if child survives the bound
            if (child.lb <= bestUB) {
                // you *can* try UB here to tighten bestUB early, but it’s not required
                auto ub_try = greedyUB_from_partial(C, child.assign);
                int ub_val = ub_try.first;
                if (ub_val < bestUB) {
                    bestUB = ub_val;
                    bestAssign = ub_try.second;
                    ub_list.push_back(bestUB);
                }
                if (child.lb <= bestUB) open.push_back(std::move(child));
            }
        }
    }

    if (!bestAssign.empty() && bestAssign[0]!=-1){
        X.assign(n, vector<int>(n,0));
        for (int i=0;i<n;++i) if (bestAssign[i]>=0 && bestAssign[i]<n) X[i][bestAssign[i]]=1;
    }
    return make_tuple(X, ub_list, node_count);
}





//question 2 
vector<vector<int>> myDynamicProgramming(int n, int c, int V[], int W[])
{
    vector<vector<int>> DP(n+1, vector<int>(c+1, 0));
    for (int i=1;i<=n;++i){
        int val = V[i-1], wt = W[i-1];
        for (int w=0; w<=c; ++w){
            int notake = DP[i-1][w];
            int take = notake;
            if (wt<=w){
                int cand = DP[i-1][w-wt] + val;
                if (cand > take) take = cand;
            }
            DP[i][w] = take;
        }
    }
    return DP;
}

vector<int> myBitmask(int n, int c, int V[], int W[])
{
    vector<vector<int>> DP = myDynamicProgramming(n, c, V, W);
    vector<int> Z(n,0);
    int w=c;
    for (int i=n; i>=1; --i){
        if (DP[i][w] == DP[i-1][w]) Z[i-1]=0;
        else { Z[i-1]=1; w -= W[i-1]; if (w<0) w=0; }
    }
    return Z;
}
