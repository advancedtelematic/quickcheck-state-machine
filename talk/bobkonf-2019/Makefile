SOURCE=slides.md
TARGET=slides.pdf

all:
	pandoc -t beamer $(SOURCE) -o $(TARGET) --bibliography=references.bib

clean:
	rm $(TARGET)
