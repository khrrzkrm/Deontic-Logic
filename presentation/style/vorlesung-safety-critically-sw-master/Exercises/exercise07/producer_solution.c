#include <time.h>
#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <tessla_debug.h>

int messages[100];
int numMessages = 0;

int generate() {
  static int lastMessageId = 0;
  usleep(100000 + rand() % 100000);
  lastMessageId += 1;
  printf("Generate %i.\n", lastMessageId);
  fflush(stdout);
  tessla_debug(1, (int64_t) lastMessageId);
  return lastMessageId;
}

void process(int id) {
  tessla_debug(2, (int64_t) id);
  usleep(100000 + rand() % 100000);
  printf("Process %i.\n", id);
  fflush(stdout);
}

void produce() {
  int id = generate();
  messages[numMessages] = id;
  numMessages += 1;
}

int consume() {
  if (numMessages > 0) {
    int i = rand() % numMessages;
    int id = messages[i];
    for (int j = i; j < numMessages - 1; j++) {
      messages[j] = messages[j + 1];
    }
    messages[numMessages] = 0;
    numMessages -= 1;
    process(id);
    return 1;
  }
  return 0;
}

int main() {
  srand(time(NULL));
  for (int i = 0; i < 30; i++) {
    if (rand() % 2) {
      consume();
    } else {
      produce();
    }
  }
  while(consume());
  return 0;
}

