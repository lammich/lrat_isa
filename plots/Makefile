all: cdf_streaming.png ovh_wtime_streaming.png ovh_mrs_streaming.png

%.png: %.pdf
	pdftoppm -singlefile -png -scale-to 1000 "$<" "$*"

%.pdf: %.tex
	pdflatex "$<"

clean:
	rm -f *.pdf *.png *.log *.aux
