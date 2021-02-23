#include <stdlib.h>
#include <stdio.h>

int main(void){
    char* buffer = (char*) malloc(129);
    *buffer='a';

    printf("%s\n", *buffer);

    return 0;
}
