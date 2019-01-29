all:
	-[ -e classes ] || mkdir classes
	scalac -d classes src/parse.scala
	chmod +x mini-dafny
	chmod +x src/vcgen.py
