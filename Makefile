.PHONY: clean all

WARNINGS := -Wall -Wextra -Wpadded -Wunused -Wno-array-bounds -Wno-comment

WITH_ZLIB ?= 0
LDFLAGS_WITH_ZLIB_0 = 
LDFLAGS_WITH_ZLIB_1 = -lz
LDFLAGS := $(LDFLAGS_WITH_ZLIB_$(WITH_ZLIB))

SRC := main.c class_file.h arena.h str.h array.h

all: micro-kotlin_debug_san micro-kotlin_debug micro-kotlin

micro-kotlin_debug_san: $(SRC)
	$(CC) $(CFLAGS) -O0 -g3 -fno-omit-frame-pointer -fpie $(WARNINGS) -std=c99 -fsanitize=address,undefined main.c -o $@ $(LDFLAGS)

micro-kotlin_debug: $(SRC)
	$(CC) $(CFLAGS) -O0 -g3 -fno-omit-frame-pointer -fpie $(WARNINGS) -std=c99 main.c -o $@ $(LDFLAGS)

micro-kotlin: $(SRC)
	$(CC) $(CFLAGS) -Ofast -g3 -fno-omit-frame-pointer -fpie $(WARNINGS) -std=c99 -march=native main.c -o $@ $(LDFLAGS)

clean:
	rm *.class || true
	rm -r META-INF/ || true

