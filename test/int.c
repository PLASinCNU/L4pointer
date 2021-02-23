#include <stdlib.h>
#include <stdio.h>

int main(void){
    int* buffer;
    int a = 3;
    if(a > 4 )
        buffer = (int*) malloc(sizeof(int)*2);
    else buffer = (int*) malloc(sizeof(int)*70);
    *buffer=1;

    printf("%d\n", *buffer);

    return 0;
}


