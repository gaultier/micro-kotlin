.PHONY: clean all

WARNINGS := -Wall -Wextra -Wpadded -Wunused -Wno-array-bounds -Wno-comment

LDFLAGS := -lz

all: micro-kotlin_debug_san micro-kotlin_debug micro-kotlin

micro-kotlin_debug_san: main.c class_file.h
	$(CC) $(CFLAGS) -O0 -g3 -fno-omit-frame-pointer -fpie $(WARNINGS) -std=c99 -fsanitize=address,undefined main.c -o $@ $(LDFLAGS)

micro-kotlin_debug: main.c class_file.h
	$(CC) $(CFLAGS) -O0 -g3 -fno-omit-frame-pointer -fpie $(WARNINGS) -std=c99 main.c -o $@ $(LDFLAGS)

micro-kotlin: main.c class_file.h
	$(CC) $(CFLAGS) -Ofast -g3 -fno-omit-frame-pointer -fpie $(WARNINGS) -std=c99 -march=native main.c -o $@ $(LDFLAGS)


clean:
	rm *.class || true
	rm -r META-INF/ || true

