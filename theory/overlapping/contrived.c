#include <stdlib.h>
#include <stdio.h>

struct node_type {
  int                val;
  struct node_type*  next;
  struct node_type*  fd;
};

typedef struct node_type    node;

node* start;
node* mod[4];

void init() {
  start = 0;
  int i;
  for (i=0;i<4;i++) mod[i] = (node*)(mod+i-2);
}

node* createNode(int v) {

  // make node and set its value
  node* c = (node*) malloc(sizeof(node));
  c->val = v;

  // add c to inclist
  node* p = (node*) (&start - 1);
  while ((p->next != 0) && (p->next)->val < v)  p = p->next;
  c->next = p->next;
  p->next = c;

  // add c to a class
  p = (node*) (mod + (v%4) - 2);
  c->fd = p->fd;
  p->fd = c; 
  
  return c;
}

void setNode(node* c, int w) {
  
  // set c's new value, caching the old one
  int v = c->val;
  c->val = w;
  
  // remove c from inclist 
  node* p = (node*) (&start - 1);
  while (p->next != c) p = p->next;
  p->next = c->next;
  
  // return c to inclist
  p = (node*) (&start - 1);
  while ((p->next != 0) && (p->next)->val < w) p = p->next;
  c->next = p->next;
  p->next = c;
  
  // remove c from its old class
  p = (node*) (mod + (v%4) - 2);
  while (p->fd != c) p = p->fd;
  p->fd = c->fd;
  
  // add c to its new class
  p = (node*) (mod + (w%4) - 2);
  c->fd = p->fd;
  p->fd = c;
}


void printState() {
  node* c = (node*) (&start - 1);
  printf("Inclist = [");
  while (c->next != 0) {
    c = c->next;
    printf("%d, ", c->val);
  };
  printf("]\n");
  printf("Classes = [");
  int i;
  for (i=0; i<4; i++) {
    printf("{");
    node* t = (node*) (mod + i - 2);
    c=t;
    while(c->fd != t) {
      c = c->fd;
      printf("%d, ", c->val);
    };
    printf("}, ");
  };
  printf("]\n");
}

int main() {
  printf("Starting program.\n");
  fflush(stdout);
  init();
  printState();
  fflush(stdout);
  node* cs[10] = {
    createNode(4), createNode(2),
    createNode(1), createNode(4),
    createNode(8), createNode(7),
    createNode(9), createNode(5),
    createNode(6), createNode(3)
  };
  printState();
  fflush(stdout);
  setNode(cs[2], 7);
  printState();
  fflush(stdout);
  setNode(cs[8], 8);
  printState();
  fflush(stdout);
  printf("Finished successfully.\n");
  return 0;
}
