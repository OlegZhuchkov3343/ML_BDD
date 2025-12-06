#include <bdd.h>
#include <fstream>

# define A 6
# define B 3343
# define C 18
# define V1 ((A+B) % 28) + 1
# define V2 ((A+C) % 2) + 1
# define V3 (A % 4) + 1

# define N 9 // число объектов (и значений свойства)
# define SQRT_N 3 // с округлением вверх (для расположения на поле)
# define M 4 // число свойств
# define LOG_N 4
# define POW2_N 16 
# define N_TRAIT_VAR N * M * LOG_N  // число булевых переменных для описания свойств объектов
# define LOOP false

using namespace std;

ofstream out;

bdd p[M][N][POW2_N];
char var [ N_TRAIT_VAR ];

/* 
v1 = 18:
. * . - "left"
. 0 .
. * .  - "right"
v2 = 1 - horizontal loop
however, does not change solution for the neighbor relationship described above
using v2 = 2 - vertical loop to showcase the algorithm working
layout:
012
345
678
generalized for n=SQRT_N:
012......n-1
n........2*n-1
..........
n*(n-1)..n^2-1
*/ 
unsigned get_neighbor_left(unsigned i, bool loop=false){
    if (i - SQRT_N > N)
        if (loop)
            return N - SQRT_N + i;
        else
            return N; // coordinate N means undefined
    else
        return i - SQRT_N;
}

unsigned get_neighbor_right(unsigned i, bool loop=false){
    if (i + SQRT_N > N - 1)
        if (loop)
            return i + SQRT_N - N;
        else
            return N;
    else
        return i + SQRT_N;
}

void print (void){
    for ( unsigned i = 0; i < N ; i ++){
        out << i << ": ";
        for ( unsigned j = 0; j < M ; j ++){
            unsigned J = i* M * LOG_N + j * LOG_N ;
            unsigned num = 0;
            for ( unsigned k = 0; k < LOG_N ; k ++) num += ( unsigned ) (var [ J + k ] << k ) ;
                out << num << ' ';
        }
        out << endl;
    }
    out << endl;
}

void build (char * varset, unsigned n, unsigned I){
    if (I == n - 1){
        if (varset[I] >= 0){
            var[I] = varset[I];
            print();
            return;
        }
        var[I] = 0;
        print();
        var[I] = 1;
        print();
        return;
    }
    if (varset[I] >= 0){
        var[I] = varset[I];
        build(varset, n, I + 1);
        return;
    }
    var[I] = 0;
    build(varset, n, I + 1);
    var[I] = 1;
    build(varset ,n , I + 1);
}

void fun(char * varset, int size){
    build(varset, size, 0);
}

void make_p_funcs(){
    for (unsigned k = 0; k < M; k++){
        for (unsigned i = 0; i < N; i++){
            for (unsigned j = 0; j < POW2_N; j++){
                p[k][i][j] = bddtrue;
                for (unsigned bit = 0; bit < LOG_N; bit++)
                    p[k][i][j] &= ((j >> bit) & 1) 
                        ? bdd_ithvar(i*M*LOG_N + k*LOG_N + bit) : bdd_nithvar(i*M*LOG_N + k*LOG_N + bit);
            }
        }
    }
}

bdd restrict_type_1(bdd F, unsigned k, unsigned i, unsigned j){
    return F & p[k][i][j];
}

bdd restrict_type_2(bdd F, unsigned k1, unsigned j1, unsigned k2, unsigned j2){
    for (unsigned i = 0; i < N; i++)
        F &= (p[k1][i][j1] & p[k2][i][j2]) | (!p[k1][i][j1] & !p[k2][i][j2]); // p[k1,i,j1] <=> p[k2,i,j2]
    return F;
}

bdd restrict_type_3(bdd F, unsigned k1, unsigned j1, unsigned k2, unsigned j2, bool left=true){
    for (unsigned i = 0; i < N; i++){
        unsigned neighbor_i = (left) ? get_neighbor_left(i, LOOP) : get_neighbor_right(i, LOOP);
        if (neighbor_i == N){
            F &= !p[k2][i][j2] & !p[k1][(left) ? get_neighbor_left(i, true) : get_neighbor_right(i, true)][j1];}
        else
            F &= (p[k1][neighbor_i][j1] & p[k2][i][j2]) 
                | (!p[k1][neighbor_i][j1] & !p[k2][i][j2]); // p[k1,neighbor,j1] <=> p[k2,i,j2]
    }
    return F;
}

bdd restrict_type_4(bdd F, unsigned k1, unsigned j1, unsigned k2, unsigned j2){
    F &= restrict_type_3(bddtrue, k1, j1, k2, j2, true) | restrict_type_3(bddtrue, k1, j1, k2, j2, false);
    return F;
}

bdd restrict_type_5(bdd F){
    for (unsigned i1 = 0; i1 < N; i1++)
        for (unsigned i2 = i1+1; i2 < N; i2++){
            bdd temp = bddtrue;
            if (i1 != i2)
                for (unsigned k = 0; k < M; k++)
                    for (unsigned j = 0; j < N; j++)
                        temp &= bdd_imp(p[k][i1][j], !p[k][i2][j]); //no two objects have equal traits
            F &= temp;
        }
    return F;
}

bdd restrict_type_6(bdd F){
    for (unsigned i = 0; i < N; i++)
        for (unsigned k = 0; k < M; k++){
            bdd temp = bddtrue;
            for (unsigned j = N; j < POW2_N; j++)
                temp &= !p[k][i][j]; //trait can't be a value higher than N
            F &= temp;
        }
    return F;
}

int main (void) {
    cout << "Данные варианта: v1 - " << V1 << "; v2 - " << V2 << "; v3 - " << V3 << endl;
    bdd_init(100000000, 1000000);
    bdd_setvarnum(N_TRAIT_VAR);
    make_p_funcs();
    cout << "p_func_done" << endl;
    bdd g = bddtrue;

    g = restrict_type_6(g);
    cout << "restrict 6" << endl;
    
    g = restrict_type_1(g, 0, 0, 0);
    g = restrict_type_1(g, 1, 1, 1);
    g = restrict_type_1(g, 2, 2, 2);
    g = restrict_type_1(g, 3, 3, 3);
    g = restrict_type_1(g, 0, 4, 4);
    g = restrict_type_1(g, 1, 5, 5);
    g = restrict_type_1(g, 2, 6, 6);
    g = restrict_type_1(g, 1, 8, 0);
    g = restrict_type_1(g, 0, 2, 1);
    cout << "restrict 1" << endl;

    g = restrict_type_2(g, 0, 8, 3, 8);
    g = restrict_type_2(g, 1, 7, 2, 7);
    g = restrict_type_2(g, 2, 6, 1, 6);
    g = restrict_type_2(g, 3, 5, 0, 5);
    g = restrict_type_2(g, 0, 4, 3, 4);
    cout << "restrict 2" << endl;

    g = restrict_type_3(g, 0, 5, 1, 3, false);
    g = restrict_type_3(g, 3, 7, 2, 3, false);
    g = restrict_type_3(g, 1, 1, 1, 4);
    g = restrict_type_3(g, 2, 4, 3, 0);
    g = restrict_type_3(g, 3, 2, 0, 3);

    cout << "restrict 3" << endl;

    g = restrict_type_4(g, 1, 6, 0, 3);
    g = restrict_type_4(g, 2, 1, 2, 5);
    g = restrict_type_4(g, 0, 6, 3, 7);
    g = restrict_type_4(g, 3, 6, 1, 5);
    cout << "restrict 4" << endl;

    g = restrict_type_5(g);
    cout << "restrict 5" << endl;

    

    out.open ("out.txt");
    out << bdd_nodecount(g) << " nodes" << endl; 
    long long satcount = (long long)bdd_satcount(g);
    cout << satcount << " solutions\n" << endl;
    out << satcount << " solutions:\n" << endl;
    if (satcount > 0) bdd_allsat(g, fun);
    out.close();

    return 0;
}

