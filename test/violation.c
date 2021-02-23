#include <stdio.h>
#include <stdlib.h>

int main(void)
{
    char* ptr = (char*) malloc(24);

    ptr[25] = 'b';

    printf("%c\n", ptr[25]);
}

