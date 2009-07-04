%.bitly:V: $HOME/www/drop/%.pdf
	rsync -avP $prereq linux.cs.tufts.edu:www/drop/$stem.pdf
	# do nothing
 