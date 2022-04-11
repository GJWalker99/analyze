create:
	        singularity build --fakeroot analyze.sif analyze.def
run:
	        ./analyze.sif
