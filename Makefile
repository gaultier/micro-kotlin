.PHONY: test_debug test_release clean

WARNINGS := -Wall -Wextra -Wpadded -Wunused -Wno-array-bounds -Wno-comment

main_debug: main.c class_file.h
	$(CC) $(CFLAGS) -DPG_WITH_LOG=1 -O0 -g3 $(WARNINGS) -std=c99 -fsanitize=address,undefined $< -o $@  $(LDFLAGS)

clean:
	rm *.class || true
	rm -r META-INF/ || true

test_debug: main_debug clean
	for f in kotlin_corpus/*.kt; do echo $$f; ./$< "$$f" || true;  done
	for f in *.class; do echo $$f; java `basename -s .class $$f`;  done

test_release: main_release clean
	for f in kotlin_corpus/*.kt; do echo $$f; ./$< "$$f" || true;  done
	for f in *.class; do echo $$f; java `basename -s .class $$f`;  done

main_release: main.c class_file.h
	$(CC) $(CFLAGS) -O2 -g3 $(WARNINGS) -std=c99 -march=native $< -o $@ -Wl,--gc-sections -fwhole-program $(LDFLAGS)

