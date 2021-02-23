#include <stdio.h>
#include <stdlib.h>

int main(void)
{
    char* ptr = (char*) malloc(100);
    char* under;
    under = ptr;
    under++;
    under--;
    printf("ptr:%p, under:%p\n", ptr, under);
    *under = 'a';
    
    printf("%c\n", *under);
}

