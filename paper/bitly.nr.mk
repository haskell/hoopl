%.bitly:V: $HOME/www/pubs/%.pdf
	rsync -avP $prereq linux.cs.tufts.edu:www/pubs/$stem.pdf
	# do nothing
