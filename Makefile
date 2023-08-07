.PHONY: test_debug test_release clean

OPTS :=  -c /usr/lib/jvm/java-17-openjdk-amd64/jmods 

WARNINGS := -Wall -Wextra -Wpadded -Wunused -Wno-array-bounds -Wno-comment

LDFLAGS := -lz

main_debug: main.c class_file.h
	$(CC) $(CFLAGS) -O0 -g3 $(WARNINGS) -std=c99 -fsanitize=address,undefined main.c -o $@  $(LDFLAGS)

clean:
	rm *.class || true
	rm -r META-INF/ || true

test_debug: clean main_debug
	for f in kotlin_corpus/*.kt; do echo $$f; ./main_debug $(OPTS) "$$f" || true;  done
	for f in **/*.class; do echo $$f; (cd `dirname $$f`; java `basename -s .class $$f`);  done

test_release: clean main_release
	for f in kotlin_corpus/*.kt; do echo $$f; ./main_release $(OPTS) "$$f" || true;  done
	for f in **/*.class; do echo $$f; (cd `dirname $$f`; java `basename -s .class $$f`);  done

main_release: main.c class_file.h
	$(CC) $(CFLAGS) -O2 -g3 $(WARNINGS) -std=c99 -march=native main.c -o $@ -Wl,--gc-sections $(LDFLAGS)

