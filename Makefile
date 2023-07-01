.PHONY: test

test: main_debug
	for f in kotlin_corpus/*.kt; do echo $$f; ./$< "$$f";  done


main_debug: main.c class_file.h
	$(CC) -DPG_WITH_LOG=1 -O0 -g3 -Wall -Wextra -std=c99 -fsanitize=address,undefined $< -o $@ 

main_release: main.c class_file.h
	$(CC) -O2 -g3 -Wall -Wextra -std=c99 -march=native $< -o $@ -Wl,--gc-sections -fwhole-program
