#include <stdlib.h>
#include <stdio.h>

int main(void){
    char* buffer;
    int a = 3;
    if(a > 4 )
        buffer = (char*) malloc(20);
    else buffer = (char*) malloc(130);
    *buffer='a';

    printf("%s\n", *buffer);

    return 0;
}

