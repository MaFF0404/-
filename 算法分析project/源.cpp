#include<iostream>
#include<vector>
#include<string>
#include<fstream>
#include<cmath>
#include<algorithm>
using namespace std;
typedef pair<int, int> PII;
int T, H, primal_OPT, SGT_OPT;
vector<int> P, D, L, U, S, A, B;
vector<int> dA, dB;

/* read the information from "input.txt" , format : 
T
H
Price (size = T)
Demand (size = T)
lower bound (size = T + 1)
upper bound (size = T + 1)
*/

void read(string filename)
{
    cout << "-----initial variables-----" << endl;
    string info;
    ifstream inStream(filename);
    int cnt = 0;
    while (cnt <= 5 && getline(inStream, info))
    {
        if (!cnt)
        {
            for (int i = 0; i < info.length(); i++)
            {
                T *= 10;
                T += info[i] - 48;
            }
            cout << "T = " << T << endl;
        }
        else if (cnt == 1)
        {
            for (int i = 0; i < info.length(); i++)
            {
                H *= 10;
                H += info[i] - 48;
            }
            cout << "H = " << H << endl;
        }
        else if (cnt == 2)
        {
            int t = 0;
            for (int i = 0; i < info.length(); i++)
            {
                if (info[i] == ' ')
                {
                    P.push_back(t);
                    t = 0;
                }
                else
                {
                    t *= 10;
                    t += info[i] - 48;
                }
            }
            P.push_back(t);
        }
        else if (cnt == 3)
        {
            int t = 0;
            for (int i = 0; i < info.length(); i++)
            {
                if (info[i] == ' ')
                {
                    D.push_back(t);
                    t = 0;
                }
                else
                {
                    t *= 10;
                    t += info[i] - 48;
                }
            }
            D.push_back(t);
        }
        else if (cnt == 4)
        {
            int t = 0;
            for (int i = 0; i < info.length(); i++)
            {
                if (info[i] == ' ')
                {
                    L.push_back(t);
                    t = 0;
                }
                else
                {
                    t *= 10;
                    t += info[i] - 48;
                }
            }
            L.push_back(t);
        }
        else if (cnt == 5)
        {
            int t = 0;
            for (int i = 0; i < info.length(); i++)
            {
                if (info[i] == ' ')
                {
                    U.push_back(t);
                    t = 0;
                }
                else
                {
                    t *= 10;
                    t += info[i] - 48;
                }
            }
            U.push_back(t);
        }
        cnt++;
    }
    inStream.close();
}

/* precompute the bound At and Bt */

void precompute()
{
    cout << "-----before apply (7)-----" << endl;
    int sum_D = 0, x, y;
    vector<int> a, b;
    
    for (int i = 0; i < T; i++)
    {
        int x, y;
        sum_D += D[i];
        x = L[i + 1] - L[0] + sum_D;
        y = U[i + 1] - U[0] + sum_D;
        if (x % H) x = x / H + 1;
        else x = x / H;
        y = y / H;

        /* the value of At and Bt before apply constraints (7) */

        if (x < 0) x = 0;
        a.push_back(x);
        if (y > T) y = T;
        b.push_back(y);
    }
    
    cout << "At : ";
    for (auto x : a) cout << x << " ";
    cout << endl;
    cout << "Bt : ";
    for (auto x : b) cout << x << " ";
    cout << endl;

    cout << "-----after apply (7)-----" << endl;
    int cur = a[0];
    A.push_back(cur);
    /* front traverse */
    for (int i = 1; i < a.size(); i++)
    {
        /* keep non-decrease */
        if (a[i] == cur + 1) cur = a[i];
        /* keep increase in eack step at most 1 */
        else if (a[i] > cur + 1)
        {
            cur = a[i];
            int j = i - 1, t = cur;
            while (j >= 0)
            {
                t -= 1;
                if (A[j] >= t) break;
                A[j] = t;
                j -= 1;
            }
        }
        A.push_back(cur);
    }

    cur = b[b.size() - 1];
    B.push_back(cur);
    /* back traverse */
    for (int i = b.size() - 2; i >= 0; i--)
    {
        /* keep non-increase */
        if (b[i] == cur - 1) cur = b[i];
        /* keep decrease in eack step at most 1 */
        else if (b[i] < cur - 1)
        {
            cur = b[i];
            int j = i + 1, t = b[i];
            while (j < b.size())
            {
                t += 1;
                if (B[b.size() - 1 - j] <= t) break;
                B[b.size() - 1 - j] = t;
                j += 1;
            }
        }
        if (cur <= i + 1) B.push_back(cur);
        else B.push_back(i + 1);
    }
    reverse(B.begin(), B.end());

    /* the value of At and Bt after apply constraints (7) */

    cout << "At : ";
    for (auto x : A) cout << x << " ";
    cout << endl;
    cout << "Bt : ";
    for (auto x : B) cout << x << " ";
    cout << endl;
    cout << endl;
}

vector<int> primal_greedy(vector<int> A, vector<int> B)
{
    /* sort price in increasing order */
    vector<PII> pri;
    for (int i = 0; i < T; i++)
    {
        pri.push_back({ P[i], i });
    }
    sort(pri.begin(), pri.end());

    vector<int> res;
    for (int i = 0; i < T; i++) res.push_back(0);

    for (int i = 0; i < T; i++)
    {
        /* find ta and tb according to j = x* then update At and Bt */
        /* set x* = 1 for greedy */
        int j = pri[i].second;
        if (!j && B[0] > 0)
        {
            res[0] = 1;
            primal_OPT += P[0];

            int ta = 0;
            while (ta + 1 < T && A[ta + 1] == 0) ta += 1;
            ta += 1;

            for (int u = ta; u < T; u++) A[u] --;
            for (int u = 0; u < T; u++) B[u] --;      
        }
        else if (A[j - 1] < B[j])
        {
            if (A[j - 1] < A[T - 1] || P[j] < 0)
            {
                res[j] = 1;
                primal_OPT += P[j];

                int ta = j, tb = j;
                while (ta + 1 < T && A[ta + 1] == A[j - 1]) ta += 1;
                ta += 1;
                while (tb - 1 >= 0 && B[tb - 1] == B[j]) tb -= 1;

                for (int u = ta; u < T; u++) A[u] --;
                for (int u = tb; u < T; u++) B[u] --;
            }
        }
    }
    return res;
}

inline int lowbit(int x) 
{
    return x & (-x);
}

/* in segment tree, each updata change 1 node in each level, which change log(T) values */

void updataA(int x, int num)
{
    while (x < T) 
    {
        dA[x] += num;
        x += lowbit(x);
    }
}

void updataB(int x, int num)
{
    while (x < T)
    {
        dB[x] += num;
        x += lowbit(x);
    }
}

/* Q query the value of A[x] and B[x] */

int QA(int x)
{
    int res = A[x];
    while (x)
    {
        res += dA[x];
        x -= lowbit(x);
    }
    return res;
    
}

int QB(int x)
{
    int res = B[x];
    while (x)
    {
        res += dB[x];
        x -= lowbit(x);
    }
    return res;
}

vector<int> SGT_greedy(vector<int> A, vector<int> B)
{
    /* segment tree : d record changes at each level */
    for (int i = 0; i <= T; i++)
    {
        dA.push_back(0);
        dB.push_back(0);
    }

    /* sort price in increasing order */

    vector<PII> pri;
    for (int i = 0; i < T; i++)
    {
        pri.push_back({ P[i], i + 1 });
    }
    sort(pri.begin(), pri.end());

    vector<int> res;
    for (int i = 0; i < T; i++) res.push_back(0);

    for (int i = 0; i < T; i++)
    {
        /* find ta and tb according to j = x* then update At and Bt */
        /* set x* = 1 for greedy */
        int j = pri[i].second;
        if (j == 1 && QB(1) > 0)
        {
            res[0] = 1;
            SGT_OPT += P[0];

            int ta = 1;
            while (ta + 1 <= T && QA(ta + 1) == 0) ta += 1;
            ta += 1;

            /* decrease value from A[ta] to A[T] by 1 */

            updataA(ta, -1);
            updataA(T + 1, 1);

            /* decrease value from B[1] to B[T] by 1 */

            updataB(1, -1);
            updataB(T + 1, 1);
        }
        else if (QA(j - 1) < QB(j))
        {
            if (QA(j - 1) < QA(T - 1) || P[j - 1] < 0)
            {
                res[j - 1] = 1;
                SGT_OPT += P[j - 1];

                int ta = j, tb = j;
                while (ta + 1 <= T && QA(ta + 1) == QA(j - 1)) ta += 1;
                ta += 1;
                while (tb - 1 > 0 && QB(tb - 1) == QB(j)) tb -= 1;

                /* decrease value from A[ta] to A[T] by 1 */

                updataA(ta, -1);
                updataA(T + 1, 1);

                /* decrease value from B[tb] to B[T] by 1 */

                updataB(tb, -1);
                updataB(T + 1, 1);
            }
        }
    }
    return res;
}

int main()
{
    vector<int> t;
    read("input.txt");
    cout << "The Price is : " << endl;
    for (auto x : P) cout << x << " ";
    cout << endl;
    cout << "The Demand is : " << endl;
    for (auto x : D) cout << x << " ";
    cout << endl;
    cout << "The lower bound is : " << endl;
    for (auto x : L) cout << x << " ";
    cout << endl;
    cout << "The upper bound is : " << endl;
    for (auto x : U) cout << x << " ";
    cout << endl;
    cout << endl;

    precompute();

    for (int i = 0; i < T; i++)
    {
        if (A[i] > B[i])
        {
            cout << "Error cause : do not satisfy (10)" << endl;
            return 0;
        }
    }

    vector<int> primal_res;
    primal_res = primal_greedy(A, B);
    cout << "-----The solution of primal greedy-----" << endl;
    cout << "OPT : " << primal_OPT << endl;
    cout << "The vector x is : " << endl;
    for (auto x : primal_res) cout << x << " ";
    cout << endl;

    cout << endl;

    /* set value of A and B start from index 1, in order to imply segment tree */

    A.insert(A.begin(), 0);
    B.insert(B.begin(), 0);
    vector<int> UF_res;
    UF_res = SGT_greedy(A, B);
    cout << "-----The solution of SGT greedy-----" << endl;
    cout << "OPT : " << SGT_OPT << endl;
    cout << "The vector x is : " << endl;
    for (auto x : UF_res) cout << x << " ";
    cout << endl;

    cout << "-----Press ENTER to stop-----" << endl;
    getchar();
    return 0;
}