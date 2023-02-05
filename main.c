#include<stdio.h>
#include<stdlib.h>

# define PAI( x ) ( x - 1 ) / 2
# define FILHO_ESQ( x ) ( 2 * x + 1 )
# define FILHO_DIR( x ) ( 2 * x + 2 )

// GRAFO

typedef struct grafo* Grafo;
struct grafo {
    double** A;
    int n; // número de vértices
    int m; // número de arestas
};

Grafo inicializaGrafo(int n) {
    int i, j;
    Grafo G = malloc(sizeof * G);
    G->n = n;
    G->m = 0;
    G->A = malloc(n * sizeof(double*));
    for (i = 0; i < n; i++)
        G->A[i] = malloc(n * sizeof(double));
    for (i = 0; i < n; i++)
        for (j = 0; j < n; j++) {
            G->A[i][j] = 0.0;
        }
    return G;
}

void insereArcoGrafo(Grafo G, int v, int w, double pComprimentoCorredor) {
    if (G->A[v][w] == 0.0) {
        G->A[v][w] = pComprimentoCorredor;

        // manter a simetria da matriz para evitar perda de informações em consultas
        G->A[w][v] = pComprimentoCorredor;

        G->m++;
    }
}

void insereTubulacao(Grafo G, int v, int w) {
    G->A[v][w] = 1.0;

    // manter a simetria da matriz para evitar perda de informações em consultas
    G->A[w][v] = 1.0;
}

// HEAP

typedef struct elem {
    int chave; // dist será guardada aqui
    int conteudo; // o vértice será guardado aqui
} Elem;

void troca(Elem* a, Elem* b) {
    Elem aux = *a;
    *a = *b;
    *b = aux;
}

void troca_pos(int* a, int* b) {
    int aux = *a;
    *a = *b;
    *b = aux;
}

// até que as propriedades do heap sejam restauradas, sobe o elemento em v[pos_elem_v]
void sobeHeap(Elem v[], int pos_v[], int pos_elem_v) {
    int f = pos_elem_v;
    while (f > 0 && v[PAI(f)].chave > v[f].chave) {
        troca(&v[f], &v[PAI(f)]);
        troca_pos(&pos_v[v[f].conteudo], &pos_v[v[PAI(f)].conteudo]);
        f = PAI(f);
    }
}

int insereHeap(Elem v[], int pos_v[], int m, Elem x) {
    v[m] = x;
    pos_v[x.conteudo] = m;
    sobeHeap(v, pos_v, m);
    return m + 1;
}

// até que as propriedades do heap sejam restauradas, desce o elemento em v[pos_elem_v] 
void desceHeap(Elem v[], int pos_v[], int m, int pos_elem_v) {
    int p = pos_elem_v, f;
    while (FILHO_ESQ(p) < m && (v[FILHO_ESQ(p)].chave < v[p].chave || (FILHO_DIR(p) < m && v[FILHO_DIR(p)].chave < v[p].chave))) {
        f = FILHO_ESQ(p);
        if (FILHO_DIR(p) < m && v[FILHO_DIR(p)].chave < v[f].chave)
            f = FILHO_DIR(p);
        troca(&v[p], &v[f]);
        troca_pos(&pos_v[v[p].conteudo], &pos_v[v[f].conteudo]);
        p = f;
    }
}

int removeHeap(Elem v[], int pos_v[], int m, Elem* px) {
    *px = v[0];
    troca(&v[0], &v[m - 1]);
    troca_pos(&pos_v[v[0].conteudo], &pos_v[v[m - 1].conteudo]);
    desceHeap(v, pos_v, m, 0);
    return m - 1;
}

void atualizaHeap(Elem v[], int pos_v[], Elem x) {
    int pos_x_v = pos_v[x.conteudo]; // pega a posição de x em v
    v[pos_x_v].chave = x.chave; // atualiza a chave de x em v
    sobeHeap(v, pos_v, pos_x_v); 
}

// ALGORITMO DE DIJKSTRA

void DijkstraComHeap ( Grafo G , int origem , int destino, double *dist , int *pred ) {
    int i , * pos_H, v , w , tam_H ;
    double custo;
    Elem * H , elem_aux ;
 
    // inicializando distâncias e predecessores
    for ( i = 0; i < G->n; i++) {
        dist[i] = 29029.2;
        pred[i] = -1;
    }


    dist [ origem ] = 0 ;

    // criando um min heap em H com vetor de posições pos_H
    H = malloc ( G -> n * sizeof( Elem ));
    pos_H = malloc ( G -> n * sizeof( int ));
    for ( i = 0 ; i < G -> n ; i ++) {
        H[i].chave = dist[i]; // chave é a "distância" do vértice
        H[i].conteudo = i; // conteúdo é o rótulo do vértice
        pos_H[i] = i; // vértice i está na posição i do heap H
    }

    troca (& H [ 0 ], & H [ origem ]); // coloca origem no início do heap H
    troca_pos (& pos_H [ 0 ], & pos_H [ origem ]); // atualiza posição
    tam_H = G -> n ;

    while ( tam_H > 0 ) { // enquanto não visitar todo vértice
 
        // buscando vértice v que minimiza dist[v]
        tam_H = removeHeap( H , pos_H , tam_H , & elem_aux );
        v = elem_aux.conteudo;
        if (v == destino) {
            break;
        }
 
        // percorrendo lista com vizinhos de v
        for (i = 0; i < G->n; i++ ) {

            if(G->A[v][i] != 0){
                w = i;
                custo = G->A[v][i];

                // e atualizando as distâncias e predecessores quando for o caso
                if ( dist [ w ] > dist [ v ] + custo ) {
                    dist [ w ] = dist [ v ] + custo ;
                    pred [ w ] = v ;
                    elem_aux.chave = dist [ w ];
                    elem_aux.conteudo = w ;
                    atualizaHeap( H , pos_H , elem_aux );
                }
            }
        }
    }

    free ( H );
    free ( pos_H );
} 

// FUNÇÃO AUXILIAR

double calculaDistancia(Grafo G, int sala, int *pred) {
    double distancia = 0;
    int verticeAtual = 0;
    int predecessor;

    while (verticeAtual != sala) {
        predecessor = pred[verticeAtual];
        distancia += G->A[verticeAtual][predecessor];
        verticeAtual = pred[verticeAtual];
    }

    return distancia;
}

int main() {

	int M /*num salas*/, E/*num corredores*/, N/*num tubulações*/, C/*num consultas*/;
	int U, V; // salas
	double D; //comprimento do corredor
    int S; // sala do impostor
    double* dist;
    int* pred;

    Grafo GrafoTripulante;
    Grafo GrafoImpostor;

	scanf("%d %d %d %d", &M, &E, &N, &C);

    // inicializando os grafos
    GrafoTripulante = inicializaGrafo(E);
    GrafoImpostor = inicializaGrafo(E);

    // inicializando os vetores de distâncias e predecessores
    dist = malloc(GrafoTripulante->n * sizeof(double));
    pred = malloc(GrafoTripulante->n * sizeof(int));

    // inserindo os arcos referentes aos corredores entre as salas
	for (int i = 0; i < ((3 * E)/3); i++) {
		scanf("%d%d%lf", &U, &V, &D);
        insereArcoGrafo(GrafoTripulante, U, V, D);
        insereArcoGrafo(GrafoImpostor, U, V, D);
	}

    // inserindo os arcos referentes a tubulação entre as salas no grafo do impostor
    for (int j = 0; j < ((2 * N) / 2); j++) {
        scanf("%d%d", &U, &V);
        insereTubulacao(GrafoImpostor, U, V);
    }

    // guardando as salas em que o tripulante avista o impostor em ação
    int* salasImpostor = malloc(C * sizeof(int));
    for (int k = 0; k < C; k++) {
        scanf("%d", &S);
        salasImpostor[k] = S;
    }
    
    // operando as consultas
    for (int i = 0; i < C; i++) {

        DijkstraComHeap(GrafoTripulante, salasImpostor[i], 0, dist, pred);

        double distanciaTripulante = calculaDistancia(GrafoTripulante, salasImpostor[i], pred);


        DijkstraComHeap(GrafoImpostor, salasImpostor[i], 0, dist, pred);

        double distanciaImpostor = calculaDistancia(GrafoImpostor, salasImpostor[i], pred);


        if (distanciaTripulante <= distanciaImpostor) {

            printf("victory\n");

        }
        else {

            printf("defeat\n");

        }
    }

	return 0;
}