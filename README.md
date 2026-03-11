Project: GPR to DIGGS Converter Script version 0.1

Creator: James Hansenbury

Main Purpose: Data In for DIGGS format, Basic Visualization

Description: Python script which reads through a given directory, reads parsable data files, and packages all relevant files into diggs zip. Creates preliminary figures for quick viewing by user.
* File types with support for diggs xml geometry: .shp
* File types with support for figure generation: .shp, .grd

Requirements: Python 3 with the following packages:
* Native packages: os, sys, datetime, pathlib, csv, zipfile, getpass, warnings
* pip-installable packages: lxml, numpy, pyproj, pandas, geopandas, rasterio, matplotlib
* Optional Packages: reverse_geocoder, ezdxf

How to Run:  
The script works as a typical shell script; insufficient or invalid arguments will prevent the script from starting, and "-h" will print the help message. The main required argument is the path to the directory that the script will analyze.
Arguments allow: toggling off interactive mode for script, converting the folder structure to DIGGS xml+zip, generating the figures, and displaying any .dxf files found in the folder (not recommended due to high computation requirements)
The GPR survey being analyzed should be in a separate folder with only GPR-associated files within it.

A documentation text file can be included for parsing by program, with key: value pairs. Example documentation file has more information on this. Equipment documentation can also be associated with each shapefile to provide metadata, example csv file provides relevant headers.
After the script starts, metadata will be determined by (in this order): file-imported metadata, user-created documentation files, values input by user during script run (if interactive mode is on), default values determined within script.
* Notes:
relying on default values will reduce descriptive capabilities of DIGGS xml.  
Script can be used to package only interpretations / processed data without geography, but a reference point must be provided for the project.
