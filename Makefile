.PHONY: test

test: main_release debug_release
	for f in *.java; do ./main_release "$$f" && ./debug_release "$$f"; done


main_debug: main.c class_file.h
	$(CC) -DPG_WITH_LOG=1 -O0 -g3 -Wall -Wextra -std=c99 -fsanitize=address,undefined -fsanitize-trap=undefined $< -o $@ 

debug_debug: debug.c class_file.h
	$(CC) -O0 -g3 -Wall -Wextra -std=c99 -fsanitize=address $< -o $@


main_release: main.c class_file.h
	$(CC) -O2 -g3 -Wall -Wextra -std=c99 -march=native $< -o $@ -Wl,--gc-sections -fwhole-program

debug_release: debug.c class_file.h
	$(CC) -O2 -g3 -Wall -Wextra -std=c99 -march=native $< -o $@
