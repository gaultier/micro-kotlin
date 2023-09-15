.PHONY: clean all

WARNINGS := -Wall -Wextra -Wpadded -Wunused -Wno-array-bounds -Wno-comment

LDFLAGS := -lz

all: main_debug main_release

main_debug: main.c class_file.h
	$(CC) $(CFLAGS) -O0 -g3 -fno-omit-frame-pointer -fpie $(WARNINGS) -std=c99 -fsanitize=address,undefined main.c -o $@  $(LDFLAGS)

main_release: main.c class_file.h
	$(CC) $(CFLAGS) -Ofast -g3 -fno-omit-frame-pointer -fpie $(WARNINGS) -std=c99 -march=native main.c -o $@ $(LDFLAGS)


clean:
	rm *.class || true
	rm -r META-INF/ || true

