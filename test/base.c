#include <stdio.h>
#include <stdlib.h>

int main(void)
{
    int a=3;
    char* ptr = (char*) malloc(100);
    char* ptr_; 
    ptr[0]='a';
    printf("a: %d\n", a);
    printf("%c\n", ptr[0]);
    ptr_ = &ptr[1];
    printf("propagated: %p -> %p\n", &ptr[1], ptr_);
    *ptr_ = 'c';
    printf("saved\n");
    printf("%c\n", *ptr_);
}
