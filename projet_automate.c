#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#define N 5000               // on définit un N grand qui nous servira à construire de grandes piles et matrices


typedef struct stack {               // définition du type d'une pile
    int stack[N];
    int top;
} stack;


typedef struct matrice {                  // définition du type d'une matrice (pas forcément carrée)
    int size1;
    int size2;
    int** tab;
} matrice;



/* @requires : size1 et size2 >= 0
   @assigns : nothing
   @ensures : create a matrix of size size1 x size2
*/
matrice create_matrice(int s1, int s2) {
    matrice m;
    m.size1 = s1;
    m.size2 = s2;
    m.tab = (int**) malloc(s1 * sizeof(int*));           // création de la colonne de pointeurs
    for (int i = 0; i < s1; i++) {
        m.tab[i] = calloc(s2, sizeof(int));             // création de chacune des lignes de la matrice
    }
    return m;
}



/* @requires : nothing
   @assigns : nothing
   @ensures : print each element of the matrix
*/
void print_matrice(matrice m) {
    int i, j;
    for (i = 0; i < m.size1; i++) {
        for (j = 0; j < m.size2; j++) {
            printf("%8d", m.tab[i][j]);             // affichage de chaque élément de la matrice
        }
        printf("\n");
    }
}


/* @requires: nothing
   @assigns: nothing
   @ensures: return an empty stack 
*/

stack new() {
    stack w;
    w.top = -1;         // w.top vaut -1 donc la pile est bien vide
    return w;
}



/* @requires: nothing
   @assigns: nothing
   @ensures: return if s is empty or not 
*/
int isEmpty(stack w) {
    return (w.top < 0);             // retourne 1 si la pile est vide et 0 sinon
}



/* @requires: nothing
   @assigns: s.stack, s.top
   @ensures: put e on the top of s 
*/
void push(stack *w, int t) {
    if (w->top == N-1) {
        printf("Stack is full");        // on ne peut pas ajouter d'éléments à une pile remplie, on informe l'utilisateur
        return;
    }
    w->top += 1;
    w->stack[w->top] = t;           // on rajoute 1 au top et e au sommet de la pile
}



/* @requires: nothing
   @assigns: s.top
   @ensures: return and remove the last element of s
*/
int pop(stack *w) {
    if (isEmpty(*w)) {
        printf("Stack is empty, cannot pop last element");      // on ne peut pas enlever d'élément à la liste vide, on informe l'utlisateur
        return 0;
    }
    int t = w->stack[w->top];
    w->top -= 1;                    // on enlève 1 au top et on retire l'élément au sommet de la pile
    return t;
}



/* @requires: nothing
   @assigns: nothing
   @ensures: print s without deleting it
*/
void print_stack(stack *w) {
    stack t = *w;                 // On utilise une copie de s pour ne pas la modifier
    while (!isEmpty(t)) {
        printf("%d\n", pop(&t));        // on affiche les éléments de la copie de s, tout en les enlevant un à un de la pile
    }
    printf("\n");
}



/* @requires : nothing
   @assigns : nothing
   @ensures : return the number of states of the file
*/

int nb_etat(const char* file){
    int n;
    FILE* f = fopen(file, "rb");         
    if (f == NULL){
        printf("No file found");            // on vérifie que l'on a bien un fichier de trouvé 
    }
    else{
        fscanf(f, "a %i", &n);             // on cherche le nombre d'états en sachant qu'il se trouve sur l première ligne sous la forme 'a n' 
    }
    fclose(f);
    return n;
}



/* @requires : nothing
   @assigns : nothing
   @ensures : store the actions of the automaton in a matrix m
*/

matrice enregistre_actions(const char* file){
    int n = nb_etat(file);                               // on initialise n par le nombre d'états du fichier
    FILE* f = fopen(file, "rb");
    if (f == NULL){                                     // on vérifie que l'on a bien un fichier de trouvé 
        printf("No file found");
        return create_matrice(1, 1);
    }
    else{
        matrice m = create_matrice(n, 128);              // on crée notre matrice de remplissage
        int c;
        char buffer[8];
        fgets(buffer, 30, f);                             // passe la première ligne 
        for (int i = 0; i < n; i++){
            for (int j = 0; j < 128; j++){
                c = fgetc(f);                           // parcourt le fichier action par action
                m.tab[i][j] = c;                        // stocke les valeurs des actions dans la matrice m
            }
        }
    return m;
    }
    fclose(f);
}



/* @requires : nothing
   @assigns : nothing
   @ensures : store the values of the firsts components of 'reduit' of the automaton in a matrix m
*/

matrice reduit_p1(const char*file){
    int n = nb_etat(file);                                      // on initialise n par le nombre d'états du fichier
    FILE* f = fopen(file, "rb");
    if (f == NULL){                                             // on vérifie que l'on a bien un fichier de trouvé 
        printf("No file found");
        return create_matrice(1, 1);
    }
    else{
        matrice m = create_matrice(1, n);                      // on crée notre matrice de remplissage
        int c;
        char buffer[8];
        fgets(buffer, 30, f);                                  // passe la première ligne 
        fseek(f, n*128  + 1, SEEK_CUR);                            // passe les éléments déjà stocké
        for (int i = 0; i < n; i++){
            c = fgetc(f);                                   // parcourt le fichier action par action
            m.tab[0][i] = c;                                // stocke les valeurs des secondes composantes de réduit dans la matrice m
        }
    return m;
    }
    fclose(f);
}



/* @requires : nothing
   @assigns : nothing
   @ensures : store the values of the seconds components of 'reduit' of the automaton in a matrix m
*/

matrice reduit_p2(const char*file){
    int n = nb_etat(file);                                   // on initialise n par le nombre d'états du fichier
    FILE* f = fopen(file, "rb");
    if (f == NULL){                                         // on vérifie que l'on a bien un fichier de trouvé 
        printf("No file found");
        return create_matrice(1, 1);
    }
    else{
        matrice m = create_matrice(1, n);                    // on crée notre matrice de remplissage
        int c;
        char buffer[8];
        fgets(buffer, 30, f);                                 // passe la première ligne 
        fseek(f, n*129 + 2, SEEK_CUR);                           // passe les éléments déjà stocké
        for (int i = 0; i < n; i++){
            c = fgetc(f);                                   // parcourt le fichier action par action
            m.tab[0][i] = c;                               // stocke les valeurs des deuxièmes composantes de réduit dans la matrice m
        }
    return m;
    }
    fclose(f);
}



/* @requires : nothing
   @assigns : nothing
   @ensures : store the values of all the triplet from the 'decale' function
*/

matrice enregistre_decale(const char*file){
    int n = nb_etat(file);                                   // on initialise n par le nombre d'états du fichier
    FILE* f = fopen(file, "rb");
    if (f == NULL){                                         // on vérifie que l'on a bien un fichier de trouvé 
        printf("No file found");
        return create_matrice(1, 1);
    }
    else{
        int c;
        int i = 0;
        char buffer[8];
        fgets(buffer, 30, f);                                 // passe la première ligne 
        fseek(f, n*130 + 3, SEEK_CUR);                        // passe les éléments déjà stocké
        matrice m = create_matrice(N,3);                      // on crée une matrice assez grande pour stocker les triplets de décale
        matrice tmp = create_matrice(1,3);                    // on crée une matrice ligne qui va stocker un à un les triplets
        c = fgetc(f);
        tmp.tab[0][0] = c;
        c = fgetc(f);
        tmp.tab[0][1] = c;
        c = fgetc(f);
        tmp.tab[0][2] = c;
        while (tmp.tab[0][0] != 173 || tmp.tab[0][1] != 173 || tmp.tab[0][2] != 173){       // condition pour nous dire que l'on a terminé de lire les triplets de décale
            m.tab[i][0] = tmp.tab[0][0];
            m.tab[i][1] = tmp.tab[0][1];
            m.tab[i][2] = tmp.tab[0][2];
            c = fgetc(f);
            tmp.tab[0][0] = c;
            c = fgetc(f);                                                               // on stocke les triplets de décale
            tmp.tab[0][1] = c;
            c = fgetc(f);
            tmp.tab[0][2] = c;
            i++;
        }
        if (i == 0){
            printf("No 'decale triplet' found");                    // on vérifie que l'on a au moins 1 triplet de trouvé
            return create_matrice(1, 1);
        }
        else{
            matrice M = create_matrice(i,3);
            for (int j = 0; j < i; j++){
                M.tab[j][0] = m.tab[j][0];
                M.tab[j][1] = m.tab[j][1];                      // on stocke les triplets dans une matrice de bonne taille
                M.tab[j][2] = m.tab[j][2];
            }
            return M;
        }
    }
    fclose(f);
}



/* @requires : nothing
   @assigns : nothing
   @ensures : store the values of all the triplet from the 'branchement' function
*/

matrice enregistre_branchement(const char*file){
    int n = nb_etat(file);                                   // on initialise n par le nombre d'états du fichier
    FILE* f = fopen(file, "rb");
    if (f == NULL){                                         // on vérifie que l'on a bien un fichier de trouvé 
        printf("No file found");
        return create_matrice(1, 1);
    }
    else{
        int c;
        int i = 0;
        char buffer[8];
        fgets(buffer, 30, f);                                  // passe la première ligne 
        fseek(f, n*130 + 3, SEEK_CUR);                         // passe les éléments déjà stocké
        matrice m = create_matrice(N,3);                       // on crée une matrice assez grande pour stocker les triplets de décale
        matrice tmp = create_matrice(1,3);                    // on crée une matrice ligne qui va stocker un à un les triplets
        c = fgetc(f);
        tmp.tab[0][0] = c;
        c = fgetc(f);
        tmp.tab[0][1] = c;
        c = fgetc(f);
        tmp.tab[0][2] = c;
        while (tmp.tab[0][0] != 173 || tmp.tab[0][1] != 173 || tmp.tab[0][2] != 173){       // on passe les triplets de décale
            c = fgetc(f);
            tmp.tab[0][0] = c;
            c = fgetc(f);
            tmp.tab[0][1] = c;
            c = fgetc(f);
            tmp.tab[0][2] = c;
        }
        c = fgetc(f);
        tmp.tab[0][0] = c;
        c = fgetc(f);
        tmp.tab[0][1] = c;
        c = fgetc(f);
        tmp.tab[0][2] = c;
        while (tmp.tab[0][0] != 173 || tmp.tab[0][1] != 173 || tmp.tab[0][2] != 173){       // condition pour nous dire que l'on a terminé de lire les triplets de branchement
            m.tab[i][0] = tmp.tab[0][0];
            m.tab[i][1] = tmp.tab[0][1];
            m.tab[i][2] = tmp.tab[0][2];
            c = fgetc(f);
            tmp.tab[0][0] = c;
            c = fgetc(f);                                                      // on stocke les triplets de branchement
            tmp.tab[0][1] = c;
            c = fgetc(f);
            tmp.tab[0][2] = c;
            i++;
        }
        if (i == 0){
            printf("No 'branchement triplet' found");                   // on vérifie que l'on a au moins 1 triplet de trouvé
            return create_matrice(1, 1);
        }
        else{
            matrice M = create_matrice(i,3);
            for (int j = 0; j < i; j++){
                M.tab[j][0] = m.tab[j][0];
                M.tab[j][1] = m.tab[j][1];                               // on stocke les triplets dans une matrice de bonne taille
                M.tab[j][2] = m.tab[j][2];
            }
            return M;
        }
    }
    fclose(f);
}



/* @requires : 127 >= s >=0 and w not empty
   @assigns : stack w
   @ensures : pops n states and stacks the 'branchement' state involved
*/

void reduit_branchement(int s, stack *w, const char*file){
    matrice r1 = reduit_p1(file);
    matrice r2 = reduit_p2(file);
    int n = r1.tab[0][s];
    int A = r2.tab[0][s];                                       // on récupère le couple (n, A) associé à réduit(s) 
    while (n > 0){                                             // on s'arrête lorsque n est nul, ie lorsque l'on a plus besoin de dépiler d'états
        pop(w);                                                 // on dépile n états
        n--;
    }
    matrice b = enregistre_branchement(file);
    int i = 0;
    while (b.tab[i][0] != w->stack[w->top] || b.tab[i][1] != A){            // on cherche branchement(s', A)
        i++;
    }
    push(w, b.tab[i][2]);                                               // on empile branchement(s', A)
}



/* @requires : 127 >= s >=0 and w not empty
   @assigns : stack w
   @ensures : stacks the 'decale' state involved
*/

void decale(int s, int c, stack *w, const char*file){
    matrice d = enregistre_decale(file);
    int i = 0;
    while(d.tab[i][0] != s || d.tab[i][1] != c){                // on cherche décale(s, c)
        i++;
    }
    push(w, d.tab[i][2]);                              // on empile décale(s, c)
}



/* @requires : nothing
   @assigns : nothing
   @ensures : prints 'Accepted' if the string is accepted by the automaton and 'Rejected' otherwise
*/

void fct_finale(const char*file){
    stack w = new();
    push(&w, 0);                            // on crée notre pile avec comme seul élément l'état initial 0
    int s, c, act;
    matrice a = enregistre_actions(file);
    char caractere[256];
    fgets(caractere, 256, stdin);           // on récupère la chaîne de caractères donnée par l'utilisateur
    int i = 0;
    while (caractere[i] != '\0'){
        i++;                                // on trouve la taille de cette chaîne de caractères
    }
    int n = 0;
    while (n <= i){                          // on s'arrête au maximum lorsque l'on finit de lire la chaîne de caractère et le '\n' (i correspond à sa taille)
        s = w.stack[w.top];
        c = (int) caractere[n];
        act = a.tab[s][c];
        if (act == 0){
            printf("Rejected\n");           // si action(s, c) = 0, on la chaîne de caractères est rejetée
            if (caractere[n] == '\n'){
                printf("Le problème vient de l'action(%i,%i) qui correspond au caractère 'retour à la ligne' de position %i et de code ASCII : %i.\n", s, c, n, caractere[n]);
            }
            else{
                printf("Le problème vient de l'action(%i,%i) qui correspond au caractère %c de position '%i' et de code ASCII '%i'.\n", s, c, caractere[n], n, caractere[n]);
            for (int k = 0; k <= n; k++){
                if (k == n){
                    printf("'%c'", caractere[k]);
                }
                else{
                    printf("%c", caractere[k]);
                }            
            }      
            printf(" <- Erreur\n");
            }
            return;
        }
        else if (act == 1){
            printf("Accepted\n");           // si action(s, c) = 1, on la chaîne de caractères est acceptée
            return;
        }
        else if (act == 2){
            decale(s, c, &w, file);          // si action(s, c) = 2, on empile décale(s, c)
            n++;                            // n++ permet de passer au caractère suivant
        }
        else if (act == 3){
            reduit_branchement(s, &w, file);        // si action(s, c) = 3, on dépile n états, on empile branchement(s', c) et on ne passe pas au caractère suivant
        }
    }
}





int main(int argc, char **argv){                                                              // test dans le main
    printf("File '%s' correctly read. Please enter your inputs.\n", argv[1]);
    fct_finale(argv[1]); 
}