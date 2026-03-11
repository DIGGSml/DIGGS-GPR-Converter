#! usr/bin/python3

# 
# GPR-to_DIGGS conversion script
# Version 0.1
# Author: James Hansenbury
# Created for DIGGS Hackathon 2026
# 

# 
# Convert various GPR-related results file types and wraps them in DIGGS file
# Also provides optionality for creating simple figures from result files, plotted in perception-neutral colors
# 

# 
# Script Structure Miniguide:
#   1. Global variables and defaults
#   2. General utility functions
#   3. User input functions
#   4. Define documentation strings
#   5. xml utilities (ie. id constructors)
#   6. Generate DIGGS xml elements
#   7. Parsing geographic files
#   8. Plotting functions
#   9. Main initializer script
#   10. Argument parsing from command line call
# 
# Tasks for adding new supported file types:
#   1. Map file extension, descriptions, and any associated file extensions or documentation into the global dictionaries
#   2. Add function importing the file type and loading it into the DIGGS structure correctly
#   3. Add function from 2. call to main function, fitting it into prioritization of geometry, etc
# 
# Dev: Areas which need work are commented with "Dev:" for an easy ctrl+F search 
# 
# Dev: Major tasks: Read .grd files and save raster points directly in DIGGS xml (not difficult, but would greatly increase size of xml file.(ie. 500 X 500 per slice with 5 slices = 1,250,000 points))
#                   Create figures directly from resulting diggs xml file rather than from source file: allows future plotting of any diggs xml file and more standardized plotting
#                     -alternatively, allow reading of zipped diggs file to create/show images from source files
#                   Add optionality to have multiple surveys based on folder structure
#                   Use classes for different file types instead of complex and confusing dictionaries
# 

import os
import sys
import datetime
from pathlib import Path
import csv
import zipfile
import getpass
import warnings
from lxml import etree as ET
import numpy as np
import pyproj
import pandas as pd
import geopandas as gpd
from pandas.core.common import not_none
import rasterio
from matplotlib import pyplot as plt
from matplotlib.collections import LineCollection
import matplotlib.cm as cm
import matplotlib.colors as colors

version = "0.1" # Version of this script

diggs_ns = "http://diggsml.org/schemas/3"
gml_ns = "http://www.opengis.net/gml/3.2"
xlink_ns = "http://www.w3.org/1999/xlink"
xsi_ns = "http://www.w3.org/2001/XMLSchema-instance"
xml_ns = "http://www.w3.org/XML/1998/namespace"

namespace_map = {
                 'diggs':diggs_ns,
                 'gml':gml_ns,
                 'xlink':xlink_ns,
                 'xsi':xsi_ns,
                 'xml':xml_ns,
                }
default_root_attributes = {
                           f'{{{xsi_ns}}}schemaLocation':"http://diggsml.org/schemas/3 http://diggsml.org/schemas/3.0.0/Diggs.xsd",
                           f'{{{xml_ns}}}lang':"en",
                           }


# Dev: These dictionaries could be replaced with classes for cleaner usage
supported_file_extensions = [".shp", ".dzt", ".grd", ".dxf", ".txt"] # Import for geography or image creation
supported_file_descriptions = ["geographic shapefile", "GSSI Raw GPR data file", "geographic raster grid file (any raster will work)", "CAD file for 3-D visualization", "text file with results documentation"]
enveloped_file_extensions = [".sgy", ".pdf", ".csv"] # Don't import, but should definitely be packaged
image_extensions = [".png", ".jpg", ".gif", ".bmp", ".tiff", ".svg", ".ico"] # Packaged
shp_extensions = [".shx", ".dbf", ".prj", ".cpg", ".sbn", ".sbx", ".fbn", ".fbx"] # Associated extensions for shapefile Dev: verify the files with these extensions and add to .xml by comparing file stems, add shapefile.xml parsing to obtain shapefile metadata
dzt_extensions = [".dzg", ".dzx", ".dza", ".plt", ".tmf", ".b3d", ".bzx"] # Associated extensions for .dzt files Dev: verify the files with these extensions and add to .xml by comparing file stems
enveloped_file_extensions += image_extensions + shp_extensions + dzt_extensions


file_type_descriptions = {
                          'name_add':{'grd':" Geographic Grid", 'txt_doc':" Text", 'txt_other':" Text", 'csv':" Delineated Text File", 'sgy':" Raw GPR Data (SEG-Y)",
                                'dzt':" Raw GPR Data (GSSI DZT)", 'dxf':" Drawing", 'image_generated':" Image", 'image_other':" Image", 'shp':" Shapefile Index File (ARCGIS SHP)",
                                'pdf':" Informational", 'shp_assoc':" Shapefile Associated (ARCGIS SHP)", 'dzt_assoc':" Raw GPR Data Associated (GSSI DZT)", 'unspecified':""},
                          'document_type':{'grd':"processed data", 'txt_doc':"documentation", 'txt_other':"associated text", 'csv':"metadata or interpretation", 'sgy':"raw field data",
                                'dzt':"raw field data", 'dxf':"drawing", 'image_generated':"data visualization", 'image_other':"image", 'shp':"geographic data",
                                'pdf':"other", 'shp_assoc':"geographic data", 'dzt_assoc':"raw GPR field metadata", 'unspecified':"unknown"},
                          'mime_type':{'grd':"", 'txt_doc':"text/plain", 'txt_other':"text/plain", 'csv':"text/csv", 'sgy':"Other: application/x-segy",
                                'dzt':"Other: application/x-dzt", 'dxf':"", 'image_generated':"", 'image_other':"", 'shp':"Other: application/x-arcgis",
                                'pdf':"application/pdf", 'shp_assoc':"Other: application/x-arcgis", 'dzt_assoc':"Other: application/x-dzt",  'unspecified':""}, # Image mimetypes determined by extension later
                          }

# Values for reading documentation into DIGGS file. This is only for ease of reading/ parsing, each key value must be manually mapped into the DIGGS file.
base_equip_keys = ["proc_desc", "manufacturer", "antenn", "antenn_model", "antenn_serial", "comp_model", "comp_serial", "samp_scan", "time_range", "scan_met", "stacking"]
equip_key_questions = [
                       "Briefly describe the data collection process. (None OK) ", "str",
                       "What company manufactured the GPR unit? ", "str",
                       "What is the center value of the antenna in MHz? ", "int",
                       "What is the model of the antenna used? (None OK) ", "str",
                       "What is the serial number of the antenna? (None OK) ", "str",
                       "What is the model of the GPR logging computer? ", "str",
                       "What is the serial number of the GPR logging computer? (None OK) ", "str",
                       "How many samples per scan did the unit take? (0: None OK) ", "int",
                       "What is the time range of the unit in ns? (0: None OK) ", "int",
                       "How many scans per meter did the unit take? (0: None OK) ", "int",
                       "What is the stacking value of the unit? (0: None OK) ", "int",
                       ]

base_doc_keys = ["author", "affiliation", "project_name", "project_description", "locality", "ref_xyz", "ref_crs", "ref_lat", "ref_lon", "survey_description"]
doc_key_parsing = [
                   ["author"],
                   ["affil", "org"],
                   ["projectname"],
                   ["projectdesc"],
                   ["locality"],
                   ["referencepoint", "refpoint", "refpt", "referencexy", "refxy"],
                   ["referenceepsg", "refepsg", "referencecrs", "refcrs"],
                   ["lat"],
                   ["lon"],
                   ["surveydesc"],
                  ]
doc_key_questions = [
                    "What name should be named as author for this DIGGS file? (Default: computer's username.) ",
                    "What organization is the author affiliated with? (Default: none.) ",
                    "What is the name of this project? (Default: folder name.) ",
                    "Briefly describe this project. (Default: generic description.) ",
                    "Where is the project? (ie. city, country. Default: lat, lon) ",
                    "",
                    "",
                    "",
                    "Near what latitude is the project? (Default: average centroid of surveys) ",
                    "Near what longitude is the project? (Default: average centroid of surveys) ",
                    "Briefly describe the GPR survey. (Default: generic description.) ",
                    ]
doc_key_default = [
                    "User " + getpass.getuser(), # author
                    "", # affiliation
                    "", # project_name, Defined later in script as scanned folder's name
                    "Project using GPR investigative method.", # project_description
                    "", # locality, Defined later in the script as lat, lon location
                    "", # ref_xyz
                    "", # ref_crs
                    "", # ref_lat, Defined later as centroid of data lines
                    "", # ref_lon, Defined later as centroid of data lines
                    "", # survey_description
                    ]

# Global variables used throughout scripts
interactive = True
centroids = []
doc_text_files = []

# --- Utility functions ---
def string_replace(string, rem_list, replace=""):
    # Replaces all substrings in a list from the input string with the replacement
    out_string = string
    for rem in rem_list:
        out_string = out_string.replace(rem, replace)
    return out_string

def transform_point(input_point, inputEPSG, outputEPSG, print_output=False):
    # Converts a point or list of points from one projection to another using EPSG codes
    # Can be used in interactive interpreter (c/p definition to interpreter)
    # input_point is [x, y, ...] (or [lon, lat, ...])
    # input_point can also be an array-like of points
    # returns points in new projection with same format
    input_point = np.copy(input_point)
    input_shapesize = len(input_point.shape)
    if input_shapesize == 1:
        input_point = np.array([input_point])
    elif input_shapesize == 0:
        raise ValueError("Input must have at least one point.")
    elif input_shapesize > 2:
        raise ValueError("Input must have at most 2 dimensions as an array or array-like.")
    inputCRS = pyproj.CRS.from_epsg(inputEPSG)
    outputCRS = pyproj.CRS.from_epsg(outputEPSG)
    conversion = pyproj.Transformer.from_crs(inputCRS, outputCRS, always_xy=True)
    transformed = np.array(conversion.transform(input_point[:,0], input_point[:,1])).T
    input_point[:,0:2] = transformed # Set input points x,y to transformed to retain extra data in points
    if print_output:
        print("Transformed coordinates:\n{}".format("\n".join(["{}, {}".format(t[0], t[1]) for t in transformed])))
    if input_shapesize == 1:
        return input_point[0]
    else:
        return input_point


# --- User input functions ---
def user_bool(question:str) -> bool:
    while True:
        answer = input(question)
        if answer and answer[0].upper() == "Y" or answer == "1":
            return True
        elif answer and answer[0].upper() == "N" or answer == "0":
            return False

def user_int(question:str, min_val=None, max_val=None) -> int:
    while True:
        answer = input(question)
        try:
            answer = float(answer)
        except ValueError:
            print("Please enter an integer value.")
            continue
        if answer % 1 == 0:
            if min_val is not None and answer < min_val:
                print("Value must be at least {}".format(min_val))
            elif max_val is not None and answer > max_val:
                print("Value must be less than {}".format(max_val))
            else:
                return int(answer)
        else:
            print("Please enter an integer value.")

def user_int_split(question:str, separator=" ", expected=0, min_val=None, max_val=None) -> list[int]:
    expected = int(expected)
    while True:
        answer = input(question)
        answer_split = answer.split(separator)
        i = 0
        for i, val in enumerate(answer_split):
            try:
                if float(val) % 1 != 0:
                    print("Please enter integer values.")
                    break
                answer_split[i] = int(val)
            except ValueError:
                print("Please enter integer values.")
                break
            if min_val is not None:
                if answer_split[i] < min_val:
                    print(f"Values must be greater than {min_val}")
                    break
            if max_val is not None:
                if answer_split[i] > max_val:
                    print(f"Values must be less than {max_val}")
                    break
        if expected:
            if expected == len(answer_split):
                return answer_split
            else:
                print('Please answer with {} integers, each separated by "{}"'.format(expected, separator))

def user_float_split(question:str, separator=" ", expected=0, min_val=None, max_val=None) -> list[float]:
    expected = int(expected)
    while True:
        answer = input(question)
        answer_split = answer.split(separator)
        for i, val in enumerate(answer_split):
            try:
                answer_split[i] = float(val)
            except ValueError:
                print("Please enter numerical values.")
                break
            if min_val is not None:
                if answer_split[i] < min_val:
                    print(f"Values must be greater than {min_val}")
                    break
            if max_val is not None:
                if answer_split[i] > max_val:
                    print(f"Values must be less than {max_val}")
                    break
        if expected:
            if expected == len(answer_split):
                return answer_split
            else:
                print('Please answer with {} numbers, each separated by "{}"'.format(expected, separator))

def user_string(question:str, length_exact=0, length_min=0, length_max=200, empty_ok=False) -> str:
    if length_max and length_max < length_min:
        length_min = 0
    while True:
        answer = input(question)
        if length_exact and length_exact != len(answer):
            print("Answer must be exactly {} characters long.".format(length_exact))
        elif length_max and length_max < len(answer):
            print("Answer must be less than {} characters long.".format(length_max))
        elif length_min > len(answer):
            print("Answer must be greater than than {} characters long.".format(length_max))
        elif answer or empty_ok:
            return answer

def user_options(options, question="Which option would you like?", multiple_choice=False , none_ok=False, none_msg="None of these"):
    # Obtain response from user for choice of given options
    # options is a list of objects convertible to string
    # multiple_choice indicates whether user can choose multiple options
    # none_ok indicates that it is acceptable to choose none of the options
    # returns 0 if none_ok and none is chosen by user, otherwise returns number corresponding to options (index + 1)
    if none_ok:
        options = [none_msg] + options
    option_list = [f"{i+1-none_ok}: {options[i]}" for i in range(len(options))]
    if multiple_choice:
        question_text = "\n".join([question, "\033[93mChoose option(s) via the corresponding numbers:\033[00m"] + option_list + [">> "])
        choice = user_int_split(question_text, min_val=int(not none_ok), max_val=len(options)).sorted()
    else:
        question_text = "\n".join([question, "\033[93mChoose an option via the corresponding number:\033[00m"] + option_list + [">> "])
        choice = user_int(question_text, int(not none_ok), len(options))
    return choice

def user_crs(file, lonlat=True):
    # User determines the crs for a file
    # arg lonlat indicates whether the file can be lat, lon, False if it must be a projected (typically determined by max/min xy values)
    options = ["EPSG code", "PROJ string", "Lat, Lon of a point in the geometry's x, y plane"]
    if lonlat:
        options = ["CRS is WGS84", "CRS is NAD83"] + options
    options = [f"{i+1}: {opt}" for i, opt in enumerate(options)]
    question_text = "How would you like to specify the crs for this file?"
    while True:
        print(f"No CRS found for the geometry in this file {file.name}", "A CRS is required.")
        response = user_options(options, question_text, none_ok=True, none_msg="Local / Leave as unknown")
        if not response:
            return None
        if not lonlat:
            response += 2

        if response == 1:
            return "EPSG:4326"
        elif response == 2:
            return "EPSG:4269"
        elif response == 3:
            epsg_code = user_int("What is the EPSG code? ", 1024, 32766)
            return f"EPSG:{epsg_code}"
        elif response == 4:
            while True:
                proj_str = "+proj=" + user_string("Enter a PROJ string to parse: +proj=")
                if proj_str.replace("+proj=", ""):
                    try:
                        crs = pyproj.CRS(proj_str)
                        if crs.to_epsg() is None:
                            return f"PROJ_string:{crs.to_proj()}"
                        else:
                            return f"EPSG:{crs.to_epsg()}"
                    except pyproj.exceptions.CRSError:
                        print("PROJ string not recognized. Try again or enter empty string to try a different method.")
                else:
                    break
        elif response == 5: # Least ideal option, makes assumptions about CRS
            x, y = user_float_split("What x, y coordinates are you referencing? ", ",", 2)
            lat, lon = (361, 361)
            while 90 > lat > -90 or 360 > lon > -180:
                lat, lon = user_float_split("What is the lat, lon of this point in WGS84 coordinates? ", ",", 2, min_val=-180, max_val=180)
            unit_resp = user_int("What units does this CRS use?\n1: meters\n2: US feet\n3: International feet\n4: kilometers\n5: inches\n6: yards", 1, 6)
            units = ["m", "us-ft", "ft", "kmi", "in", "yd"]
            proj_str = f"+proj=tmerc +lat_0={lat} +lon_0={lon} +x_0={x} +y_0={y} +units={units[unit_resp-1]} +ellps=WGS84"
            try:
                crs = pyproj.CRS(proj_str)
                if crs.to_epsg() is None:
                    return f"Custom_PROJ_string:{crs.to_proj()}"
                else:
                    return f"EPSG:{crs.to_epsg()}"
            except pyproj.exceptions.CRSError:
                print("Could not generate CRS from inputs. Try again or choose a different option.")



# --- File type sorting ---
def validate_file_types(files):
    # Sorts the files in the input list into supported file type bins
    # Returns (binned files, unsupported files)
    sorted_files = {'enveloped':[]}
    for key in supported_file_extensions:
        sorted_files[key] = []
    skipped_files = []
    for file in files:
        if ".diggs" in file.name.lower():
            skipped_files.append(file) # Skip already-generated diggs files
            continue
        if file.suffix.lower() in supported_file_extensions:
            sorted_files[file.suffix].append(file)
        elif file.suffix.lower() in enveloped_file_extensions:
            sorted_files['enveloped'].append(file)
        else:
            if interactive:
                question_text = f"Could not detect file type for file:\n{file.name}\nIf this file is one of the following supported readable types, specify it as such."
                options_text = ([f"{supported_file_descriptions[i]} ({supported_file_extensions[i]})" for i in range(len(supported_file_extensions))]
                            + ["Do not import, but package all files with this extension as data."]
                            + ["Do not import, but package only this file as data."])
                choice = user_options(options_text, question_text, multiple_choice=False, none_ok=True, none_msg="Skip import of this file.")
                if not choice:
                    skipped_files.append(file)
                elif choice == len(supported_file_extensions) + 1:
                    enveloped_file_extensions.append(file.suffix)
                    sorted_files['enveloped'].append(file)
                elif choice == len(supported_file_extensions) + 2:
                    sorted_files['enveloped'].append(file)
                else:
                    sorted_files[supported_file_extensions[choice-1]].append(file)
            else:
                skipped_files.append(file)

    return (sorted_files, skipped_files)

# --- Define documentation for DIGGS file: 1. By doc file 2. By user input 3. By defaults/ file parsing ---
def parse_doc_file(files:list[Path]):
    # Verify and parse documentation file for relevant names and descriptions
    global doc_text_files
    if not files:
        return [{}, {}]
    doc_files = []
    for file in files:
        if "doc" in file.stem and "diggs" in file.stem:
            doc_files.append(file)
    if not doc_files:
        for file in files:
            if "document" in file.stem:
                doc_files.append(file)
    if not doc_files:
        for file in files:
            if "doc" in file.stem:
                doc_files.append(file)
    if not doc_files:
        doc_files = files
    for file in files:
        if file not in doc_files and "equip" in file.name:
            doc_files.append(file)
    if interactive and len(doc_files) > 1:
        index = user_options(files, "Do any of these files contain formatted documentation to load into the diggs xml?", multiple_choice=True,  none_ok=True)
        if index[0] == 0:
            return [{}, {}] 
        else:
            doc_files = [doc_files[i] for i in index]

    documentation = {}
    equipment = {}
    for file in doc_files:
        has_doc = False
        with open(file) as iFile:
            doc_text = iFile.read()
        doc_lines = doc_text.split("\n")
        for line in doc_lines:
            pair = line.split(":")
            if len(pair) > 1:
                filled = False
                # Iterate through documentation keys
                for i in range(len(base_doc_keys)):
                    if filled:
                        has_doc = True
                        break
                    if base_doc_keys[i] not in documentation.keys():
                        for str_match in doc_key_parsing[i]:
                            if str_match in string_replace(pair[0].lower(), [" ", "_", "-"]):
                                documentation[base_doc_keys[i]] = pair[1].strip()
                                filled = True
                                break
                # Iterate through equipment keys
                for key in base_equip_keys:
                    valid = True
                    for search_key in key.split("_"):
                        if search_key not in pair[0].lower():
                            valid = False
                    if valid:
                        equipment[key] = pair[1]
        if has_doc:
            doc_text_files.append(file)

    return [documentation, equipment]

def user_documentation(documentation):
    if not interactive:
        return
    keys = list(documentation.keys())
    for i, key in enumerate(base_doc_keys):
        if key not in keys and doc_key_questions[i]:
            response = user_string(doc_key_questions[i], empty_ok=True)
            if response:
                documentation[key] = response

def default_documentation(documentation):
    # Called after ref point and locality are determined
    keys = list(documentation.keys())
    for i, key in enumerate(base_doc_keys):
        if key not in keys:
            documentation[key] = doc_key_default[i]
    if not documentation['survey_description']:
        documentation['survey_description'] = f"Ground Penetrating Radar survey near {documentation['locality']}. Contains {documentation['trackline_count']} transects."

def user_equipment(equipment, tracklines_exist=True):
    # Need equipment info for survey
    if not interactive:
        return
    if not tracklines_exist:
        if not user_bool("No tracklines found, equipment metadata missing.\n\033[93mWould you like to enter the equipment metadata manually to include it in the diggs file?\033[00m "):
            return
    keys = list(equipment.keys())
    for i, key in enumerate(base_equip_keys):
        if key not in keys and equip_key_questions[2*i]:
            if equip_key_questions[2*i+1] == "int":
                response = user_int(equip_key_questions[2*i], min_val=0)
                if response:
                    equipment[key] = str(response)
            else:
                response = user_string(equip_key_questions[2*i], empty_ok=True)
                if response:
                    equipment[key] = response

def project_reference_point(documentation, centroids):
    # Set ref_point in documentation: Use existing documentation, else use centroids, else get direct input from user
    keys = documentation.keys()
    if "ref_xyz" in keys and "ref_crs" in keys: # First try to parse user's ref point from doc file
        xyz_split = documentation['ref_xyz'].split(",")
        if len(xyz_split) == 1:
            xyz_split = documentation['ref_xyz'].split(" ")
        try:
            x = float(xyz_split[0])
            y = float(xyz_split[1])
            ref_epsg = float(documentation['ref_crs']) # Dev: Add support for PROJ strings as well
            try:
                z = float(xyz_split[2])
            except (ValueError, IndexError):
                z = None
            ref_xy = transform_point((x, y), ref_epsg, 4326)
            if z is not None:
                documentation['ref_point'] = ref_xy + [z]
            else:
                documentation['ref_point'] = ref_xy
            return
        except (ValueError, IndexError):
            pass
    if "ref_lat" in keys and "ref_lon" in keys: # Then use lat, lon from doc file
        try:
            documentation['ref_point'] = [float(ref_lon), float(ref_lat)]
            return
        except ValueError:
            pass
    if centroids: # Next attempt to use centroids from tracklines
        centroid = np.average(centroids, axis=0)
        documentation['ref_point'] = centroid
        return
    elif interactive: # Finally, try to get it from user
        ref_lat, ref_lon = user_float_split("\033[93mEnter the latitude, longitude for the project reference point (WGS84)\033[00m", ",", 2, -180, 360)
        documentation['ref_point'] = [ref_lon, ref_lat]
        return
    else: # Must have reference point!
        raise ValueError("No usable reference point for project found. Run with interactive mode on or documentation file.")

def project_locality(documentation):
    try:
        import reverse_geocoder
    except ModuleNotFoundError:
        warnings.warn("\033[93mPython package 'reverse_geocoder' not found:\033[00m automatic locality determination impossible.")
        documentation['locality'] = f"Latitude: {documentation['ref_point'][1]} Longitude: {documentation['ref_point'][0]}"
        return
    locality = reverse_geocoder.search((float(documentation['ref_point'][1]), float(documentation['ref_point'][0])))
    documentation['locality'] = f"{locality['name']}, {locality['admin1']}; {locality['cc']}"

# --- Helper generation functions ---

# ID generator scripts for consistency and easy alteration
def set_project_id(int_val=1):
    project_id = f"project_gpr_{int_val:03}"
    return project_id

def set_survey_id(int_val=1):
    survey_id = f"survey_{int_val:03}"
    return survey_id

def set_survey_time_int_id(int_val=1):
    survey_time_id = f"survey_{int_val:03}_t_int"
    return survey_time_id

def set_results_id(int_val=1):
    results_id = f"results_{int_val:03}"
    return results_id

def set_proc_id(int_val=1):
    proc_id = f"procedure_{int_val:03}"
    return proc_id

def set_trackline_id(int_val=1):
    trackline_id = f"trackline_{int_val:03}"
    return trackline_id

def set_trackline_refpt_id(int_val=1):
    ref_point_id = f"trackline_{int_val:03}_ref_pt"
    return ref_point_id

def set_centerline_id(int_val=1):
    ctrline_id = f"centerline_{int_val:03}"
    return ctrline_id

def set_ctrline_lrs_id(int_val=1):
    ctrline_lrs_id = f"centerline_{int_val:03}_lrs"
    return ctrline_lrs_id

def set_track_time_int_id(int_val=1):
    track_time_int_id = f"track_ti_{int_val:03}"
    return track_time_int_id

def set_file_id(int_val=1, text="text"):
    file_id = f"file_{text}_{int_val:03}"
    return file_id

def image_mime_type(file):
    image_mime_types = {'.jpg':"image/jpeg", '.png':"image/png", '.gif':"image/gif", 'pdf':"application/pdf", '.svg':"image/svg+xml", '.webp':"image/webp", '.av1':"image/avif", '.tiff':"image/tiff", '.bmp':"image/bmp", '.ico':"image/x-icon"}
    if file.suffix.lower() in image_mime_types.keys():
        return image_mime_types[file.suffix.lower()]
    else:
        return ""

# --- DIGGS XML tree generation ---

def generate_DIGGS_root():
    # Generate DIGGS root element with proper attributes
    # Uses global default_root_attributes
    # Returns root element: base for the whole xml
    root = ET.Element(f"{{{diggs_ns}}}Diggs", nsmap=namespace_map)
    for key in default_root_attributes.keys():
        root.set(key, default_root_attributes[key])
    return root

def generate_document_info(root, documentation):
    # Generate the required document information element of the file
    # Returns document element: No actions needed
    author_id = "".join([s[0] for s in documentation['author'].split(" ")[:-1]] + [documentation['author'].split(" ")[-1]])
    affil_string = ""
    if 'affiliation' in documentation.keys() and documentation['affiliation']:
        affil_string = f" / {documentation['affiliation']}"

    # Create document info tree
    el_documentation = ET.SubElement(root, f"{{{diggs_ns}}}documentInformation")
    el_documentation = ET.SubElement(el_documentation, f"{{{diggs_ns}}}DocumentInformation")
    el_active = ET.SubElement(el_documentation, f"{{{gml_ns}}}description")
    el_active.text = documentation['doc_description']
    el_active = ET.SubElement(el_documentation, f"{{{diggs_ns}}}creationDate")
    el_active.text = documentation['file_creation'].strftime('%Y-%m-%d')
    el_active = ET.SubElement(el_documentation, f"{{{diggs_ns}}}author")
    el_active = ET.SubElement(el_active, f"{{{diggs_ns}}}refxyrefxyBusinessAssociate")
    el_active.set(f"{{{gml_ns}}}id", f"author_{author_id}")
    el_active = ET.SubElement(el_active, f"{{{gml_ns}}}name")
    el_active.text = documentation['author'] + affil_string
    el_software = ET.SubElement(el_documentation, f"{{{diggs_ns}}}sourceSoftware")
    el_software = ET.SubElement(el_software, f"{{{diggs_ns}}}SoftwareApplication")
    el_software.set(f"{{{gml_ns}}}id", f"sw_01_v{version}")
    el_active = ET.SubElement(el_software, f"{{{gml_ns}}}name")
    el_active.text = "GPR-to-DIGGS Converter Script"
    el_active = ET.SubElement(el_software, f"{{{diggs_ns}}}version")
    el_active.text = version
    return el_documentation

def generate_project_info(root, documentation, project_index=1):
    # Generate the overarching project element for the files
    # return project element: Need to add reference point
    project_id = set_project_id(project_index)

    el_project = ET.SubElement(root, f"{{{diggs_ns}}}project")
    el_project = ET.SubElement(el_project, f"{{{diggs_ns}}}Project")
    el_project.set(f"{{{gml_ns}}}id", project_id)
    el_active = ET.SubElement(el_project, f"{{{gml_ns}}}description")
    el_active.text = documentation['project_description']
    el_active = ET.SubElement(el_project, f"{{{gml_ns}}}name")
    el_active.text = documentation['project_name']
    # Add the reference point later
    return el_project

def add_project_refpoint(el_project, documentation):
    el_active = ET.SubElement(el_project, f"{{{diggs_ns}}}referencePoint")
    el_active = ET.SubElement(el_active, f"{{{diggs_ns}}}PointLocation")
    el_active.set(f"{{{gml_ns}}}id", "project_ref_point")
    el_active = ET.SubElement(el_active, f"{{{gml_ns}}}pos", srsName="EPSG:4326")
    if len(documentation['ref_point']) > 2:
        el_active.set("srsDimension", "3")
    else:
        el_active.set("srsDimension", "2")
    el_active.text = " ".join([str(val) for val in documentation['ref_point']])

def generate_field_survey(root, documentation, survey_index=1, project_index=1):
    # Generate geophysical field survey element linking all parsed/ imported data
    # Returns:
    # Survey element: neeed to add trackline ID's, survey time
    # Files element: need to add each packaged file
    # Procedure element: need to add description, equipment, and settings
    project_id = set_project_id(project_index)
    results_id = set_results_id(survey_index)
    survey_id = set_survey_id(survey_index)

    el_survey = ET.SubElement(root, f"{{{diggs_ns}}}measurement")
    el_survey = ET.SubElement(el_survey, f"{{{diggs_ns}}}GeophysicalFieldSurvey")
    el_survey.set(f"{{{gml_ns}}}id", survey_id)
    el_active = ET.SubElement(el_survey, f"{{{gml_ns}}}description")
    el_active.text = documentation['survey_description']
    el_active = ET.SubElement(el_survey, f"{{{gml_ns}}}name")
    el_active.text = f"{documentation['project_name']} GPR Field Survey"
    el_active = ET.SubElement(el_survey, f"{{{gml_ns}}}projectRef")
    el_active.set(f"{{{xlink_ns}}}href", f"#{project_id}")

    el_results = ET.SubElement(el_survey, f"{{{diggs_ns}}}outcome")
    el_results = ET.SubElement(el_results, "GP_SurveyResult")
    el_results.set(f"{{{gml_ns}}}id", results_id)
    el_datapack = ET.SubElement(el_results, f"{{{diggs_ns}}}dataPackage")
    el_datapack = ET.SubElement(el_datapack, f"{{{diggs_ns}}}DataPackage")
    el_active = ET.SubElement(el_datapack, f"{{{gml_ns}}}name")
    el_files = ET.SubElement(el_datapack, f"{{{diggs_ns}}}files") # Need to add each file to this element

    el_active = ET.SubElement(el_survey, f"{{{diggs_ns}}}geophysicalMethod")
    el_active.text = "ground penetrating radar"

    return [el_survey, el_files]

def add_trackline_id(el_survey, el_trackline):
    track_id = el_trackline[0].get(f"{{{gml_ns}}}id") # Only 1 child of samplingFeature
    el_active = ET.SubElement(el_survey, f"{{{diggs_ns}}}samplingFeatureRef")
    el_active.set(f"{{{xlink_ns}}}href", f"#{track_id}")

def add_survey_times(el_survey, documentation):
    # Add survey time to survey element

    if not all([key in documentation.keys() for key in ["survey_start", "survey_end"]]):
        return False

    survey_index = int(el_survey.get(f"{{{gml_ns}}}id").split("_")[-1])
    survey_time_id = set_survey_time_int_id(survey_index)

    el_active = ET.SubElement(el_survey, f"{{{diggs_ns}}}samplingTime")
    el_active = ET.SubElement(el_active, f"{{{diggs_ns}}}TimeInterval")
    el_active.set(f"{{{gml_ns}}}id", survey_time_id)
    el_subactive = ET.SubElement(el_active, f"{{{diggs_ns}}}start")
    el_subactive.text = documentation['survey_start']
    el_subactive = ET.SubElement(el_active, f"{{{diggs_ns}}}end")
    el_subactive.text = documentation['survey_end']
    return True

def generate_procedure(el_survey, documentation, equipment):
    excepted_keys = ["proc_desc", "antenn_model", "antenn_serial", "comp_serial", "samp_scan", "time_range", "scan_met", "stacking"] # Can skip missing values
    if not any([key in equipment.keys() for key in base_equip_keys if key not in excepted_keys]):
        return None
    
    survey_index = int(el_survey.get(f"{{{gml_ns}}}id").split("_")[-1])
    
    proc_id = set_proc_id(survey_index)
    rec_id = f"receiver_{survey_index:03}"
    src_id = f"source_{survey_index:03}"
    dacq_id = f"data_acq_{survey_index:03}"

    el_procedure = ET.SubElement(el_survey, f"{{{diggs_ns}}}procedure")
    el_procedure = ET.SubElement(el_procedure, "GP_FieldProcedure")
    el_procedure.set(f"{{{gml_ns}}}id", proc_id)

    el_active = ET.SubElement(el_procedure, f"{{{gml_ns}}}description")
    if "description" in equipment.keys():
        el_active.text = equipment['proc_desc']
    else:
        el_active.text = f"GPR survey using {equipment['antenn']} MHz antenna with continuous acquisition along transect lines."
    el_active = ET.SubElement(el_procedure, f"{{{gml_ns}}}name")
    el_active.text = f"GPR Field Procedure near {documentation['locality']}"

    el_active = ET.SubElement(el_procedure, f"{{{diggs_ns}}}receiverEquipment")
    el_active = ET.SubElement(el_active, f"{{{diggs_ns}}}GP_Receiver")
    el_active.set(f"{{{gml_ns}}}id", rec_id)
    el_subactive = ET.SubElement(el_active, f"{{{gml_ns}}}name")
    el_subactive.text = f"{equipment['antenn']} MHz Shielded Antenna (Rx)"
    el_subactive = ET.SubElement(el_active, f"{{{diggs_ns}}}class")
    el_subactive.text = "GPR antenna"
    el_subactive = ET.SubElement(el_active, f"{{{diggs_ns}}}make")
    el_subactive.text = equipment['manufacturer']
    if "antenn_model" in equipment.keys():
        el_subactive = ET.SubElement(el_active, f"{{{diggs_ns}}}modelNumber")
        el_subactive.text = equipment['antenn_model']
    if "antenn_serial" in equipment.keys():    
        el_subactive = ET.SubElement(el_active, f"{{{diggs_ns}}}serialNumber")
        el_subactive.text = equipment['antenn_serial']
    el_subactive = ET.SubElement(el_active, f"{{{diggs_ns}}}receiverType")
    el_subactive.text = "radio wave antenna"
    el_subactive = ET.SubElement(el_active, f"{{{diggs_ns}}}isGroup")
    el_subactive.text = "false"

    el_active = ET.SubElement(el_procedure, f"{{{diggs_ns}}}sourceEquipment")
    el_active = ET.SubElement(el_active, f"{{{diggs_ns}}}GP_Source")
    el_active.set(f"{{{gml_ns}}}id", src_id)
    el_subactive = ET.SubElement(el_active, f"{{{gml_ns}}}name")
    el_subactive.text = f"{equipment['antenn']} MHz Shielded Antenna (Tx)"
    el_subactive = ET.SubElement(el_active, f"{{{diggs_ns}}}class")
    el_subactive.text = "GPR antenna"
    el_subactive = ET.SubElement(el_active, f"{{{diggs_ns}}}make")
    el_subactive.text = equipment['manufacturer']
    if "antenn_model" in equipment.keys():
        el_subactive = ET.SubElement(el_active, f"{{{diggs_ns}}}modelNumber")
        el_subactive.text = equipment['antenn_model']
    if "antenn_serial" in equipment.keys():    
        el_subactive = ET.SubElement(el_active, f"{{{diggs_ns}}}serialNumber")
        el_subactive.text = equipment['antenn_serial']
    el_subactive = ET.SubElement(el_active, f"{{{diggs_ns}}}sourceType")
    el_subactive.text = "impulsive"
    el_subactive = ET.SubElement(el_active, f"{{{diggs_ns}}}isGroup")
    el_subactive.text = "false"

    el_active = ET.SubElement(el_procedure, f"{{{diggs_ns}}}dataAcquisitionSystem")
    el_active = ET.SubElement(el_active, f"{{{diggs_ns}}}GP_DataAcquisitionSystem")
    el_active.set(f"{{{gml_ns}}}id", dacq_id)
    el_subactive = ET.SubElement(el_active, f"{{{gml_ns}}}name")
    el_subactive.text = f"{equipment['manufacturer']} {equipment['comp_model']}"
    el_subactive = ET.SubElement(el_active, f"{{{diggs_ns}}}make")
    el_subactive.text = equipment['manufacturer']
    el_subactive = ET.SubElement(el_active, f"{{{diggs_ns}}}modelNumber")
    el_subactive.text = equipment['comp_model']
    if "comp_serial" in equipment.keys():    
        el_subactive = ET.SubElement(el_active, f"{{{diggs_ns}}}serialNumber")
        el_subactive.text = equipment['comp_serial']
    el_subactive = ET.SubElement(el_active, f"{{{diggs_ns}}}numberChannels")
    el_subactive.text = "1"

    el_params = ET.SubElement(el_procedure, f"{{{diggs_ns}}}recordingParameters")

    el_active = ET.SubElement(el_params, f"{{{diggs_ns}}}Parameter")
    el_subactive = ET.SubElement(el_active, f"{{{diggs_ns}}}parameterName")
    el_subactive.text = "Center Frequency"
    el_subactive = ET.SubElement(el_active, f"{{{diggs_ns}}}parameterValue")
    el_subactive.text = equipment['antenn']
    el_subactive = ET.SubElement(el_active, f"{{{diggs_ns}}}parameterUnits")
    el_subactive.text = "MHz"

    if "samp_scan" in equipment.keys():
        el_active = ET.SubElement(el_params, f"{{{diggs_ns}}}Parameter")
        el_subactive = ET.SubElement(el_active, f"{{{diggs_ns}}}parameterName")
        el_subactive.text = "Samples per Scan"
        el_subactive = ET.SubElement(el_active, f"{{{diggs_ns}}}parameterValue")
        el_subactive.text = equipment['samp_scan']

    if "time_range" in equipment.keys():
        el_active = ET.SubElement(el_params, f"{{{diggs_ns}}}Parameter")
        el_subactive = ET.SubElement(el_active, f"{{{diggs_ns}}}parameterName")
        el_subactive.text = "Time Range"
        el_subactive = ET.SubElement(el_active, f"{{{diggs_ns}}}parameterValue")
        el_subactive.text = equipment['time_range']
        el_subactive = ET.SubElement(el_active, f"{{{diggs_ns}}}parameterUnits")
        el_subactive.text = "ns"

    if "scan_met" in equipment.keys():
        el_active = ET.SubElement(el_params, f"{{{diggs_ns}}}Parameter")
        el_subactive = ET.SubElement(el_active, f"{{{diggs_ns}}}parameterName")
        el_subactive.text = "Scans per Meter"
        el_subactive = ET.SubElement(el_active, f"{{{diggs_ns}}}parameterValue")
        el_subactive.text = equipment['scan_met']
        el_subactive = ET.SubElement(el_active, f"{{{diggs_ns}}}parameterUnits")
        el_subactive.text = "1/m"

    if "stacking" in equipment.keys():
        el_active = ET.SubElement(el_params, f"{{{diggs_ns}}}Parameter")
        el_subactive = ET.SubElement(el_active, f"{{{diggs_ns}}}parameterName")
        el_subactive.text = "Stacking"
        el_subactive = ET.SubElement(el_active, f"{{{diggs_ns}}}parameterValue")
        el_subactive.text = equipment['stacking']

    return el_procedure

def generate_trackline_elements(geometry, documentation, equipment, geom_doc, id_num, project_index=1):
    # Generate tracklines
    # Requires geometry: shapely object 'geometry'
    # Returns list of trackline objects, does not append them to the root
    project_id = set_project_id(project_index)
    trackline_id = set_trackline_id(id_num)
    trkln_refpt_id = set_trackline_refpt_id(id_num)
    centerline_id = set_centerline_id(id_num)
    ctrline_lrs_id = set_ctrline_lrs_id(id_num)
    track_time_int_id = set_track_time_int_id(id_num)
    crs_units = "m" # Dev: Need to fix this to reference the actual crs


    if "survey_name" in documentation.keys():
        survey_text = f"survey {documentation['survey_name']}"
    else:
        survey_text = f"project {documentation['project_name']}"
    if "antenn" in geom_doc.keys():
        antenna_text = f" {geom_doc['antenn']} MHz antenna."
    elif "antenn" in equipment.keys():
        antenna_text = f" {equipment['antenn']} MHz antenna."
    else:
        antenna_text = ""
                 
    if geometry.has_z:
        dims = "3"
    else:
        dims = "2"

    # Create a parent element for each feature
    el_feature = ET.Element(f"{{{diggs_ns}}}samplingFeature", nsmap=namespace_map)

    el_trackline = ET.SubElement(el_feature, f"{{{diggs_ns}}}GP_Trackline")
    el_trackline.set(f"{{{gml_ns}}}id", trackline_id)
    # Add all sections from geometry and documentation
    el_active = ET.SubElement(el_trackline, f"{{{gml_ns}}}description")
    el_active.text = f"GPR transect line {id_num} for {survey_text}.{antenna_text} Cart-mounted unit with continuous acquisition."
    el_active = ET.SubElement(el_trackline, f"{{{gml_ns}}}name")
    el_active.text = f"GPR_Line-{id_num:03}"

    el_active = ET.SubElement(el_trackline, f"{{{diggs_ns}}}projectRef")
    el_active.set(f"{{{xlink_ns}}}href", f"#{project_id}")
    el_active = ET.SubElement(el_trackline, f"{{{diggs_ns}}}referencePoint")
    el_active = ET.SubElement(el_active, f"{{{diggs_ns}}}PointLocation")
    el_active.set(f"{{{gml_ns}}}id", trkln_refpt_id)
    el_active = ET.SubElement(el_active, f"{{{gml_ns}}}pos", srsName=geom_doc['crs'], srsDimensions=dims)
    el_active = ET.SubElement(el_trackline,f"{{{diggs_ns}}}centerLine")
    el_active = ET.SubElement(el_active, f"{{{diggs_ns}}}LinearExtent", srsName=geom_doc['crs'], srsDimensions=dims)
    el_active.set(f"{{{gml_ns}}}id", centerline_id)
    el_active = ET.SubElement(el_active, f"{{{gml_ns}}}posList")
    el_active.text = " ".join(np.array(geometry.coords).astype(str).flatten())

    el_active = ET.SubElement(el_trackline, f"{{{diggs_ns}}}linearReferencing")
    el_active = ET.SubElement(el_active, f"{{{diggs_ns}}}LinearSpatialReferenceSystem")
    el_active.set(f"{{{gml_ns}}}id", ctrline_lrs_id)
    el_subactive = ET.SubElement(el_active, f"{{{gml_ns}}}identifier", codeSpace="AuthorityName")
    el_subactive.text = f"AuthorityName_{ctrline_lrs_id}"
    el_active = ET.SubElement(el_active, f"{{{diggs_ns}}}lrm")
    el_active.set(f"{{{xlink_ns}}}href", "https://diggsml.org/def/crs/DIGGS/0.1/lrm.xml#distance_m")

    el_active = ET.SubElement(el_trackline, "sensorMix")
    el_active.text = "mixed"
    if "start_time" in geom_doc.keys() and "end_time" in geom_doc.keys():
        el_active = ET.SubElement(el_trackline, f"{{{diggs_ns}}}whenTracklineOccupied")
        el_active = ET.SubElement(el_active, f"{{{diggs_ns}}}TimeInterval")
        el_active.set(f"{{{gml_ns}}}id", track_time_int_id)
        el_subactive = ET.SubElement(el_active, f"{{{diggs_ns}}}start")
        el_subactive.text = geom_doc['start_time']
        el_subactive = ET.SubElement(el_active, f"{{{diggs_ns}}}end")
        el_subactive.text = geom_doc['end_time']
    el_active = ET.SubElement(el_trackline, f"{{{diggs_ns}}}totalTracklineLength", uom=crs_units)
    el_active.text =  f"{geometry.length:.03f}"

    return el_feature

def generate_file_references(files, type, parent_folder, start_index=1):
    # Creates the file reference elements
    # Files should be a list of Path objects
    # Returns a list of file ref objects
    # Does not append them to the root
    if not files:
        return []
    references = []
    index = start_index
    for file in files:
        file_string = " ".join([s.capitalize() for s in string_replace(file.stem, ["-", "_"], " ").split(" ")])
        relative_path = file.relative_to(parent_folder)
        if "image" in type:
            mime_type = image_mime_type(file)
        else:
            mime_type = file_type_descriptions['mime_type'][type]

        el_datafile = ET.Element(f"{{{diggs_ns}}}GP_FieldDataFile", nsmap=namespace_map)
        el_datafile.set(f"{{{gml_ns}}}id", set_file_id(index, type))
        el_active = ET.SubElement(el_datafile, f"{{{gml_ns}}}name")
        el_active.text = f"{file_string}{file_type_descriptions['name_add'][type]}"
        el_active = ET.SubElement(el_datafile, f"{{{diggs_ns}}}fileURL")
        el_active.text = str(relative_path)
        el_active = ET.SubElement(el_datafile, f"{{{diggs_ns}}}fileType")
        el_active.text = file.suffix.replace(".", "")
        el_active = ET.SubElement(el_datafile, f"{{{diggs_ns}}}fileType")
        el_active.text = file_type_descriptions['document_type'][type]
        
        try: # This section adapted from Google AI
            creation_date = os.path.getctime(file) # Windows
        except Exception:
            try:    
                stat = os.stat(path_to_file)
                creation_date = stat.st_birthtime # Unix creation time
            except Exception:
                try:
                    stat = os.stat(path_to_file)
                    creation_date = stat.st_ctime # Unix last update time
                except Exception:
                    creation_date = None
        
        if creation_date is not None:
            el_active = ET.SubElement(el_datafile, f"{{{diggs_ns}}}fileDate")
            el_active.text = f"{datetime.datetime.fromtimestamp(creation_date)}"
        if mime_type:
            el_active = ET.SubElement(el_datafile, f"{{{diggs_ns}}}mimeType")
            el_active.text = mime_type
        # Dev: Add this program (reference the software ID in document info section) as creating application
        # if "generated" in type:
        #     el_active = ET.SubElement(el_datafile, f"{{{diggs_ns}}}creatingApplication")
        #     el_active

        references.append(el_datafile)
    return references

# --- Parse Data Files For xml ---

def tracklines_by_dzt(dzt_files, documentation, equipment, project_index):
    # Dev: Currently placeholder script for dzt implementation
    # Loads a shapefile and converts it into the proper DIGGS gml format, adding it to the input process element
    # Dev: Determine travel direction (N, NE, E, SE, S, SW, W, NW) of each trackline based on coordinates and add to description
    #      Improve time range parsing for survey/ project time period
    #      Determine length units by crs instead of assuming meters
    global centroids
    return []
    doc_keys = ["start_time", "end_time", "crs"]
    project_id = set_project_id(project_index)
    tracklines = []
    default_doc = {}

    # Use convention of "YYYY-MM-DD" for datetime strings to determine earliest/latest time (not ideal)
    # Dev: Preferred: Parse time strings into datetime objects, then compare. (too much effort for hackathon time constraints)
    min_time = "9"
    max_time = "0"

    # First obtain/ sort all necessary metadata
    folder_tracklines = {} # trackline element for each folder, filename
    folder_crs = {} # lists of crs found for each folder
    folder_equip = {} 
    no_crs_files = [] # list of files without explicit crs to be re-analyzed and assigned one after initial round
    index = 0
    for file_path in shp_files: # Iterate through each file
        # Dev: wrap file import into a separate function to remove redundancy
        try:
            shp_df = gpd.read_file(file_path)
        except Exception:
            continue
        # Verify that the shapefile contains only linear features
        if any(shp_df.area):
            print(f"Shape file {file_path.name} contains features other than transects. Unable to import.")
            continue

        # .csv documentation should have headers describing the field, with as many rows as there are lines in the shapefile (or 1 to apply to all lines in shp file)
        csv_doc = file_path.parent / (file_path.stem + ".csv")
        if csv_doc.is_file():
            with open(csv_doc, "r", newline="") as iFile:
                reader = csv.DictReader(iFile)
                csv_rows = [row for row in reader]
                doc_lines = [{}]*len(csv_rows)
                for csv_key in csv_rows[0].keys():
                    for key in doc_keys:
                        valid = True
                        for search_key in key.split("_"):
                            if search_key not in csv_key.lower():
                                valid = False
                        if valid:
                            for i, line in enumerate(doc_lines):
                                line[key] = csv_rows[i][csv_key]
                    for key in base_equip_keys:
                        valid = True
                        for search_key in key.split("_"):
                            if search_key not in csv_key.lower():
                                valid = False
                        if valid:
                            for i, line in enumerate(doc_lines):
                                line[key] = csv_rows[i][csv_key]
                            equipment[key] = doc_lines[0][key] # Dev: Make better equipment binding to files, when adding more survey options


            # Check for times
            if "start_time" in doc_lines[0].keys:
                for line in doc_lines:
                    if line['start_time'] and min_time > line['start_time']:
                        min_time = line['start_time']
                    if max_time < line['start_time']:
                        max_time = line['start_time']
            if "end_time" in doc_lines[0].keys():
                for line in doc_lines:
                    if line['end_time'] and min_time > line['end_time']:
                        min_time = line['end_time']
                    if max_time < line['end_time']:
                        max_time = line['end_time']
        else:
            doc_lines = [default_doc]

        if "antenn" in folder_equip[file_path.parent.name].keys(): # Dev: Neglects to add antenna info if a later file in folder has it
            for line in doc_lines:
                line['antenn'] = folder_equip[file_path.parent.name]['antenn']
             
        # First attempt at CRS for this file
        no_crs = False
        if shp_df.crs is None:
            if "crs" in doc_lines[0].keys():
                if file_path.parent.name not in folder_crs.keys():
                    folder_crs[file_path.parent.name] = [doc_lines[0]['crs']]
                elif doc_lines[0]['crs'] not in folder_crs[file_path.parent.name]:
                    folder_crs[file_path.parent.name].append(doc_lines[0]['crs'])
            elif file_path.parent.name in folder_crs.keys():
                for line in doc_lines:
                    line['crs'] = folder_crs[file_path.parent.name][0] # Dev: Using first crs in folder not ideal
            else:
                no_crs = True
        else:
            for line in doc_lines:
                if "crs" in doc_lines[0].keys() and doc_lines[0]['crs'] != shp_df.crs:
                    warnings.warn("Shapefile crs does not match documentation. Using shapefile value.")
                line['crs'] = shp_df.crs
            if file_path.parent.name not in folder_crs.keys():
                folder_crs[file_path.parent.name] = [shp_df.crs]
            elif shp_df.crs not in folder_crs[file_path.parent.name]:
                folder_crs[file_path.parent.name].append(shp_df.crs)
            # Add centroid to centroids for project location
            # Dev: Parse documentation file crs to determine centroids from user-defined crs
            wgs_df = shp_df.to_crs(epsg=4326)
            shpfile_centroid = [np.average(wgs_df.centroid.x), np.average(wgs_df.centroid.y)]
            centroids.append(shpfile_centroid)

        crs_units = "m" # Dev: Need to fix this to reference the actual crs

        if no_crs:
            no_crs_files.append(file_path) # Try again after all files analyzed
            continue

        # Make trackline elements
        i = 0
        for _, row in shp_df.iterrows(): # Iterate through each line in the file
            i += 1
            if len(doc_lines) == shp_df.count().geometry:
                doc_ind = i
            elif len(doc_lines) > 1:
                warnings.warn(f"csv file and shapefile have mismatched length ({len(doc_lines)}, {shp_df.count().geometry}). Using first csv entry.")
                doc_ind = 0
            else:
                doc_ind = 0
            tracklines.append(generate_trackline_elements(row.geometry, documentation, equipment, doc_lines[doc_ind], project_index, index+i))
        index += i

    # Try again for files without crs
    for file in no_crs_files:
        try:
            shp_df = gpd.read_file(file_path)
        except Exception:
            continue
        # Verify that the shapefile contains only linear features
        if any(shp_df.area):
            print(f"\033[93mShape file {file_path.name} contains features other than transects.\033[00m Unable to import.")
            continue

        # .csv documentation should have headers describing the field, with as many rows as there are lines in the shapefile
        csv_doc = file_path.parent / (file_path.stem + ".csv")
        if csv_doc.is_file():
            with open(csv_doc, "r", newline="") as iFile:
                reader = csv.DictReader(iFile)
                csv_rows = [row for row in reader]
                doc_lines = [{}]*len(csv_rows)
                for csv_key in csv_rows[0].keys():
                    for key in doc_keys:
                        valid = True
                        for search_key in key.split("_"):
                            if search_key not in csv_key.lower():
                                valid = False
                        if valid:
                            for i, line in enumerate(doc_lines):
                                line[key] = csv_rows[i][csv_key]
                    for key in base_equip_keys:
                        valid = True
                        for search_key in key.split("_"):
                            if search_key not in csv_key.lower():
                                valid = False
                        if valid:
                                for i, line in enumerate(doc_lines):
                                    line[key] = csv_rows[i][csv_key]
                                equipment[key] = doc_lines[0][key] # Dev: Make better equipment binding to files, when adding more survey options


            # Check for times
            if "start_time" in doc_lines[0].keys:
                for line in doc_lines:
                    if line['start_time'] and min_time > line['start_time']:
                        min_time = line['start_time']
                    if max_time < line['start_time']:
                        max_time = line['start_time']
            if "end_time" in doc_lines[0].keys():
                for line in doc_lines:
                    if line['end_time'] and min_time > line['end_time']:
                        min_time = line['end_time']
                    if max_time < line['end_time']:
                        max_time = line['end_time']
        else:
            doc_lines = [default_doc]

        if "antenn" in folder_equip[file_path.parent.name].keys(): # Dev: Neglects to add antenna info if a later file in folder has it
            for line in doc_lines:
                line['antenn'] = folder_equip[file_path.parent.name]['antenn']

        # Determine crs from user input if none found in the folder
        if file.parent.name in folder_crs.keys():
            for line in doc_lines:
                line['crs'] = folder_crs[file.parent.name][0] # Dev: using first crs? Not ideal if multiple crs found in folder
        elif interactive:
            min_x = min(min([line.xy[0] for line in shp_df['geometry']]))
            max_x = max(max([line.xy[0] for line in shp_df['geometry']]))
            min_y = min(min([line.xy[1] for line in shp_df['geometry']]))
            max_y = max(max([line.xy[1] for line in shp_df['geometry']]))
            if any([min_x < -180, max_x >= 360, min_y < -90, max_y > 90]):
                latlon_possible = False
            else:
                latlon_possible = True
            crs_string = user_crs(file_path, latlon_possible)
            if not crs_string:
                continue
            elif "EPSG:" in crs_string:
                shp_df.crs = crs_string
            else: # PROJ_string
                shp_df.crs = crs_string.split(":")[1]
            for line in doc_lines:
                line['crs'] = crs_string
            folder_crs[file.parent.name] = [crs_string]
            # Add centroid to centroids for project location
            wgs_df = shp_df.to_crs(epsg=4326)
            cents = wgs_df.centroid
            shpfile_centroid = [np.average(wgs_df.centroid.x), np.average(wgs_df.centroid.y)]
            centroids.append(shpfile_centroid)

        # Make trackline elements
        i = 0
        for _, row in shp_df.iterrows(): # Iterate through each line in the file
            i += 1
            if len(doc_lines) == shp_df.count().geometry:
                doc_ind = i
            elif len(doc_lines) > 1:
                warnings.warn(f"\033[93mcsv file and shapefile have mismatched length ({len(doc_lines)}, {shp_df.count().geometry}).\033[00m Using first csv entry.")
                doc_ind = 0
            else:
                doc_ind = 0
            tracklines.append(generate_trackline_elements(row.geometry, documentation, equipment, doc_lines[doc_ind], project_index, index+i))
        index += i



def tracklines_by_shp(shp_files, documentation, equipment, project_index):
    # Loads a shapefile and converts it into the proper DIGGS gml format, adding it to the input process element
    # Dev: Determine travel direction (N, NE, E, SE, S, SW, W, NW) of each trackline based on coordinates and add to description
    #      Improve time range parsing for survey/ project time period
    #      Determine length units by crs instead of assuming meters
    global centroids
    doc_keys = ["start_time", "end_time", "crs"]
    project_id = set_project_id(project_index)
    tracklines = []
    default_doc = {}

    # Use convention of "YYYY-mm-DDTHH:MM:SS" for datetime strings to determine earliest/latest time (not ideal)
    # Dev: Preferred: Parse time strings into datetime objects, then compare. (too much effort for hackathon time constraints)
    min_time = "9"
    max_time = "0"

    # First obtain/ sort all necessary metadata
    folder_tracklines = {} # trackline element for each folder, filename
    folder_crs = {} # lists of crs found for each folder
    no_crs_files = [] # list of files without explicit crs to be re-analyzed and assigned one after initial round
    index = 0
    for file_path in shp_files: # Iterate through each file
        # Dev: wrap file import into a separate function to remove redundancy
        try:
            shp_df = gpd.read_file(file_path)
        except Exception:
            continue
        # Verify that the shapefile contains only linear features
        if any(shp_df.area):
            print(f"\033[93mShape file {file_path.name} contains features other than transects.\033[00m Unable to import.")
            continue

        # .csv documentation should have headers describing the field, with as many rows as there are lines in the shapefile (or 1 to apply to all lines in shp file)
        csv_doc = file_path.parent / (file_path.stem + ".csv")
        if csv_doc.is_file():
            with open(csv_doc, "r", newline="") as iFile:
                reader = csv.DictReader(iFile)
                csv_rows = [row for row in reader]
                doc_lines = [{}]*len(csv_rows)
                for csv_key in csv_rows[0].keys():
                    for key in doc_keys:
                        valid = True
                        for search_key in key.split("_"):
                            if search_key not in csv_key.lower():
                                valid = False
                                break
                        if valid:
                            for i, line in enumerate(doc_lines):
                                line[key] = csv_rows[i][csv_key]
                    for key in base_equip_keys:
                        if key not in equipment.keys():
                            valid = True
                            for search_key in key.split("_"):
                                if search_key not in csv_key.lower():
                                    valid = False
                            if valid:
                                for i, line in enumerate(doc_lines):
                                    line[key] = csv_rows[i][csv_key]
                                equipment[key] = doc_lines[0][key] # Dev: Make better equipment binding to files, when adding more survey options

            # Check for times
            if "start_time" in doc_lines[0].keys():
                for line in doc_lines:
                    if line['start_time'] and min_time > line['start_time']:
                        min_time = line['start_time']
                    if max_time < line['start_time']:
                        max_time = line['start_time']
            if "end_time" in doc_lines[0].keys():
                for line in doc_lines:
                    if line['end_time'] and min_time > line['end_time']:
                        min_time = line['end_time']
                    if max_time < line['end_time']:
                        max_time = line['end_time']
        else:
            doc_lines = [default_doc]

        # First attempt at CRS for this file
        no_crs = False
        if shp_df.crs is None:
            if "crs" in doc_lines[0].keys():
                if file_path.parent.name not in folder_crs.keys():
                    folder_crs[file_path.parent.name] = [doc_lines[0]['crs']]
                elif doc_lines[0]['crs'] not in folder_crs[file_path.parent.name]:
                    folder_crs[file_path.parent.name].append(doc_lines[0]['crs'])
            elif file_path.parent.name in folder_crs.keys():
                for line in doc_lines:
                    line['crs'] = folder_crs[file_path.parent.name][0] # Dev: Using first crs in folder not ideal
            else:
                no_crs = True
        else:
            for line in doc_lines:
                if "crs" in doc_lines[0].keys() and doc_lines[0]['crs'] != shp_df.crs:
                    warnings.warn("Shapefile crs does not match documentation. Using shapefile value.")
                line['crs'] = shp_df.crs
            if file_path.parent.name not in folder_crs.keys():
                folder_crs[file_path.parent.name] = [shp_df.crs]
            elif shp_df.crs not in folder_crs[file_path.parent.name]:
                folder_crs[file_path.parent.name].append(shp_df.crs)
            # Add centroid to centroids for project location
            # Dev: Parse documentation file crs to determine centroids from user-defined crs
            wgs_df = shp_df.to_crs(epsg=4326)
            shpfile_centroid = [np.average(wgs_df.centroid.x), np.average(wgs_df.centroid.y)]
            centroids.append(shpfile_centroid)

        if no_crs:
            no_crs_files.append(file_path) # Try again after all files analyzed
            continue

        # Make trackline elements
        i = 0
        for _, row in shp_df.iterrows(): # Iterate through each line in the file
            i += 1
            if len(doc_lines) == shp_df.count().geometry:
                doc_ind = i
            elif len(doc_lines) > 1:
                warnings.warn(f"\033[93mcsv file and shapefile have mismatched length ({len(doc_lines)}, {shp_df.count().geometry}).\033[00m Using first csv entry.")
                doc_ind = 0
            else:
                doc_ind = 0
            tracklines.append(generate_trackline_elements(row.geometry, documentation, equipment, doc_lines[doc_ind], project_index, index+i))
        index += i

    # Try again for files without crs
    for file in no_crs_files:
        try:
            shp_df = gpd.read_file(file_path)
        except Exception:
            continue
        # Verify that the shapefile contains only linear features
        if any(shp_df.area):
            print(f"Shape file {file_path.name} contains features other than transects. Unable to import.")
            continue

        # .csv documentation should have headers describing the field, with as many rows as there are lines in the shapefile
        csv_doc = file_path.parent / (file_path.stem + ".csv")
        if csv_doc.is_file():
            with open(csv_doc, "r", newline="") as iFile:
                reader = csv.DictReader(iFile)
                csv_rows = [row for row in reader]
                doc_lines = [{}]*len(csv_rows)
                for csv_key in csv_rows[0].keys():
                    for key in doc_keys:
                        valid = True
                        for search_key in key.split("_"):
                            if search_key not in csv_key.lower():
                                valid = False
                        if valid:
                            for i, line in enumerate(doc_lines):
                                line[key] = csv_rows[i][csv_key]
                    for key in base_equip_keys:
                        if key not in equipment.keys():
                            valid = True
                            for search_key in key.split("_"):
                                if search_key not in csv_key.lower():
                                    valid = False
                            if valid:
                                for i, line in enumerate(doc_lines):
                                    line[key] = csv_rows[i][csv_key]
                                equipment[key] = doc_lines[0][key] # Dev: Make better equipment binding to files for different surveys

            # Check for times
            if "start_time" in doc_lines[0].keys():
                for line in doc_lines:
                    if line['start_time'] and min_time > line['start_time']:
                        min_time = line['start_time']
                    if max_time < line['start_time']:
                        max_time = line['start_time']
            if "end_time" in doc_lines[0].keys():
                for line in doc_lines:
                    if line['end_time'] and min_time > line['end_time']:
                        min_time = line['end_time']
                    if max_time < line['end_time']:
                        max_time = line['end_time']
        else:
            doc_lines = [default_doc]

        # Determine crs from user input if none found in the folder
        if file.parent.name in folder_crs.keys():
            for line in doc_lines:
                line['crs'] = folder_crs[file.parent.name][0] # Dev: using first crs? Not ideal if multiple crs found in folder
        elif interactive:
            min_x = min(min([line.xy[0] for line in shp_df['geometry']]))
            max_x = max(max([line.xy[0] for line in shp_df['geometry']]))
            min_y = min(min([line.xy[1] for line in shp_df['geometry']]))
            max_y = max(max([line.xy[1] for line in shp_df['geometry']]))
            if any([min_x < -180, max_x >= 360, min_y < -90, max_y > 90]):
                latlon_possible = False
            else:
                latlon_possible = True
            crs_string = user_crs(file_path, latlon_possible)
            if not crs_string:
                continue
            elif "EPSG:" in crs_string:
                shp_df.crs = crs_string
            else: # PROJ_string
                shp_df.crs = crs_string.split(":")[1]
            for line in doc_lines:
                line['crs'] = crs_string
            folder_crs[file.parent.name] = [crs_string]
            # Add centroid to centroids for project location
            cents_wgs = shp_df.centroid.to_crs(4326)
            shpfile_centroid = [np.average(cents_wgs.x), np.average(cents_wgs.y)]
            centroids.append(shpfile_centroid)

        # Make trackline elements
        i = 0
        for _, row in shp_df.iterrows(): # Iterate through each line in the file
            i += 1
            if len(doc_lines) == shp_df.count().geometry:
                doc_ind = i
            elif len(doc_lines) > 1:
                warnings.warn(f"csv file and shapefile have mismatched length ({len(doc_lines)}, {shp_df.count().geometry}). Using first csv entry.")
                doc_ind = 0
            else:
                doc_ind = 0
            tracklines.append(generate_trackline_elements(row.geometry, documentation, equipment, doc_lines[doc_ind], project_index, index+i))
        index += i

    if "survey_start" not in documentation.keys() and min_time != "9":
        documentation['survey_start'] = min_time # Dev: With multiple surveys, turn this into a dictionary with keys corresponding to survey index
    if "survey_end" not in documentation.keys() and max_time != "0":
        documentation['survey_end'] = max_time # Dev: With multiple surveys, turn this into a dictionary with keys corresponding to survey index

    return tracklines


# --- Plotting functions ---
def colored_line(x, y, c, ax, **lc_kwargs):
    """
    *Copied directly from matplotlib's documentation page:
        https://matplotlib.org/stable/gallery/lines_bars_and_markers/multicolored_line.html

    Plot a line with a color specified along the line by a third value.

    It does this by creating a collection of line segments. Each line segment is
    made up of two straight lines each connecting the current (x, y) point to the
    midpoints of the lines connecting the current point with its two neighbors.
    This creates a smooth line with no gaps between the line segments.

    Parameters
    ----------
    x, y : array-like
        The horizontal and vertical coordinates of the data points.
    c : array-like
        The color values, which should be the same size as x and y.
    ax : Axes
        Axis object on which to plot the colored line.
    **lc_kwargs
        Any additional arguments to pass to matplotlib.collections.LineCollection
        constructor. This should not include the array keyword argument because
        that is set to the color argument. If provided, it will be overridden.

    Returns
    -------
    matplotlib.collections.LineCollection
        The generated line collection representing the colored line.
    """
    # if "array" in lc_kwargs:
    #     warnings.warn('The provided "array" keyword argument will be overridden')

    # Default the capstyle to butt so that the line segments smoothly line up
    default_kwargs = {"capstyle": "butt"}
    default_kwargs.update(lc_kwargs)

    # Compute the midpoints of the line segments. Include the first and last points
    # twice so we don't need any special syntax later to handle them.
    x = np.asarray(x)
    y = np.asarray(y)
    x_midpts = np.hstack((x[0], 0.5 * (x[1:] + x[:-1]), x[-1]))
    y_midpts = np.hstack((y[0], 0.5 * (y[1:] + y[:-1]), y[-1]))

    # Determine the start, middle, and end coordinate pair of each line segment.
    # Use the reshape to add an extra dimension so each pair of points is in its
    # own list. Then concatenate them to create:
    # [
    #   [(x1_start, y1_start), (x1_mid, y1_mid), (x1_end, y1_end)],
    #   [(x2_start, y2_start), (x2_mid, y2_mid), (x2_end, y2_end)],
    #   ...
    # ]
    coord_start = np.column_stack((x_midpts[:-1], y_midpts[:-1]))[:, np.newaxis, :]
    coord_mid = np.column_stack((x, y))[:, np.newaxis, :]
    coord_end = np.column_stack((x_midpts[1:], y_midpts[1:]))[:, np.newaxis, :]
    segments = np.concatenate((coord_start, coord_mid, coord_end), axis=1)

    lc = LineCollection(segments, **default_kwargs)
    lc.set_array(c)  # set the colors of each segment

    return ax.add_collection(lc)

# def plot_csv(csv_path:Path):
#     # Dev: Need to sort csv files, then combine the csv interpretations with tracklines, etc
#     headers = []
#     i = 0
#     header_rows = csv_header_count(csv_path)
#     with open(csv_path, newline="") as iFile:
#         csvRead = csv.reader(iFile)
#         while i < header_rows:
#             headers.append(next(csvRead))
#             i += 1
#         data = [row for row in csvRead]
#     x_ind, y_ind = (0, 1)
#     if headers:
#         headers.reverse()
#         for header_ind, line in enumerate(headers):
#             x_key, y_key, lat_key, lon_key = ("") * 4
#             for key in line:
#                 if key.lower() == "x":
#                     x_key = key
#                 elif key.lower() == "y":
#                     y_key = key
#                 elif "lat" in key.lower():
#                     lat_key = key
#                 elif "lon" in key.lower():
#                     lon_key = key
#             if x_key and y_key:
#                 break
#             elif lat_key and lon_key:
#                 x_key, y_key = (lon_key, lat_key)
#                 break
#         if x_key and y_key:
#             x_ind, y_ind = (headers[header_ind].index(x_key), headers[header_ind].index(y_key))

def plot_raster(file_path, output_path):
    # For generic raster files and grd
    # Dev: Improve .grd file reading, some .grd formats give 1.7e308 for all values
    grids = [] # List of numpy arrays
    with rasterio.open(file_path) as raster_grids:
        for index in raster_grids.indexes:
            grids.append(raster_grids.read(index))
        height = raster_grids.height
        width = raster_grids.width
    aspect_ratio = height/width
    plot_base_size = 3
    n_rows = max([1, int(np.floor(np.sqrt(len(grids))))])
    n_cols = max([1, int(np.ceil(np.sqrt(len(grids))))])

    # fig, ax = plt.subplots(n_rows, n_cols, figsize=(plot_base_size*n_cols/aspect_ratio, plot_base_size*n_rows*aspect_ratio), layout='constrained')
    fig, ax = plt.subplots(n_rows, n_cols, layout='constrained')
    try:
        iter(ax)
    except:
        ax = [ax]
    _ = fig.suptitle(f"Raster map view for file {file_path.name}")
    for i, grid in enumerate(grids):
        # print(grid.shape)
        # grid[np.isinf(grid)] = np.average(grid.flatten())
        # grid[np.isnan(grid)] = np.average(grid.flatten())
        # print(np.max(grid.flatten()))
        ind = i
        image = ax[ind].imshow(grid, cmap="inferno")
        _ = ax[ind].set_title(f"Grid value band {i+1}")
        _ = ax[ind].set_xlabel("X Coordinate")
        _ = ax[ind].set_ylabel("Y Coordinate")
        _ = ax[ind].axis('equal') # Ensure equal scaling for map view
        _ = fig.colorbar(image, ax=ax[ind])

    fig.savefig(output_path)

def plot_shapefile_transects(shp_path, output_path):
    # Loads a shapefile and plots the transects within
    shp_df = gpd.read_file(shp_path)
    # Verify that the shapefile contains only transects
    if any(shp_df.area):
        raise ValueError("Shape file contains feature(s) other than lines.")
    
    # Determine if lines should be colored for elevation
    z_vals = []
    for line in shp_df.geometry:
        if line.has_z:
            try:
                z_vals += [point[2] for point in line.coords]
            except IndexError:
                continue
    if z_vals:
        has_zvals = np.any(np.array(z_vals) - z_vals[0])
    else:
        has_zvals = False

    # Plot lines
    fig, ax = plt.subplots()
    if has_zvals:
        colormap = plt.colormaps['cividis'].copy()
        colormap.set_bad(color="black")
        normalized = colors.Normalize(vmin=min(z_vals), vmax=max(z_vals))
        mapper = cm.ScalarMappable(norm=normalized, cmap=colormap)
        _ = fig.colorbar(mapper)
    i = 0
    for line in shp_df.geometry:
        line_arr = np.array(line.coords)
        if has_zvals:
            image = colored_line(line_arr[:, 0], line_arr[:, 1], line_arr[:, 2], ax, cmap=colormap)
            _ = fig.colorbar(image, ax=ax)
        else:
            _ = ax.plot(line_arr[:,0], line_arr[:,1], color="black")
        if i:
            _ = ax.scatter(line_arr[0,0], line_arr[0,1], color="k", marker="o")
        else:
            _ = ax.scatter(line_arr[0,0], line_arr[0,1], color="k", marker="o", label="Transect Start")
        i += 1
    _ = ax.legend()
    _ = ax.set_xlabel("X coordinate")
    _ = ax.set_ylabel("Y coordinate")
    _ = ax.set_title(f"Transects for shapefile {shp_path.name}")

    fig.savefig(output_path)

def display_dxf(dxf_path):
    # Function largely generated via Google AI
    # Does not recreate dxf file, but allows user to view it with the gui
    try:
        import ezdxf
        from ezdxf.addons.drawing import Frontend, RenderContext
        from ezdxf.addons.drawing.matplotlib import MatplotlibBackend
    except ModuleNotFoundError:
        return
    try:
        doc = ezdxf.readfile(dxf_path)
    except IOError:
        print(f"File is not a .dxf file, or another I/O error occurred:\n{dxf_path}")
        return
    except ezdxf.DXFStructureError:
        print(f"Could not read .dxf file structure, possibly corrupted:\n{dxf_path}")
        return

    # Get the modelspace
    msp = doc.modelspace()

    # Create a figure and axes for matplotlib
    fig, ax = plt.subplots()
    ctx = RenderContext(doc)
    out = MatplotlibBackend(ax)

    # Render the DXF entities onto the matplotlib axes
    Frontend(ctx, out).draw_layout(msp)

    _ = ax.set_title(f"File View: {dxf_path.name}")
    _ = ax.set_xlabel("X Coordinate")
    _ = ax.set_ylabel("Y Coordinate")
    _ = ax.axis('equal') # Ensure equal scaling (assuming map view)
    _ = ax.grid(True)

    fig.show()

def plot_grid_field(grid, output_path):
    # Takes a grid array and plots the values.
    # Not currently used
    # Dev: To be used in a combo image of tracklines and interpretation points
    colormap = plt.colormaps['inferno'].copy()
    _ = plt.imshow(grid, cmap=colormap)
    plt.savefig(output_path)

# --- Main Initializing Function ---

def main(folder_path, convert=True, plot_figs=False, fig_ext=".png", display_figs=False):
    # Loads all files from a folder and converts/ packages them with simple DIGGS format as a single 
    # 
    # global documentation


    if not folder_path or not Path(folder_path).resolve().is_dir():
        raise FileNotFoundError(f"Could not find target folder:\n{folder_path}\nCheck your paths.")
    folder_path = Path(folder_path).resolve()
    doc_key_default[2] = folder_path.name

    # First decide which files to load
    all_files = [f for f in folder_path.rglob("*") if f.is_file()]
    if not all_files:
        raise FileNotFoundError(f"No files were found in target folder:\n{folder_path}\nCheck your paths.")
    sorted_files, unsorted_files = validate_file_types(all_files)

    gen_fig_files = []
    if plot_figs:
        fig_index = 1
        fig_folder = folder_path / "GPR2DIGGS_gen_figs"
        fig_folder.mkdir(exist_ok=True)
        for file in sorted_files['.grd']:
            try:
                with warnings.catch_warnings():
                    warnings.simplefilter("ignore") # ignore all warnings
                    fig_path = (fig_folder / f"diggsfig{fig_index:03}_{file.stem}{fig_ext}").resolve()
                    plot_raster(file, fig_path)
                    gen_fig_files.append(fig_path)
                    fig_index += 1
            except Exception as err:
                # print(f".grd plot error:\n{err}") # Debugging
                continue
        for file in sorted_files['.shp']:
            try:
                with warnings.catch_warnings():
                    warnings.simplefilter("ignore") # ignore all warnings
                    fig_path = (fig_folder / f"diggsfig{fig_index:03}_{file.stem}{fig_ext}").resolve()
                    plot_shapefile_transects(file, fig_path)
                    gen_fig_files.append(fig_path)
                    fig_index += 1
            except Exception as err:
                raise err # Debugging
                # print(f".shp plot error:\n{err}") # Debugging
                continue
    
    if display_figs:
        for file in sorted_files['.dxf']:
            try:
                display_dxf(file)
            except Exception as err:
                # print(f".dxf plot error:\n{err}") # Debugging
                continue

    if convert:
        # Documentation section
        documentation, equipment = parse_doc_file(sorted_files['.txt']) # First check for formatted text file
        if interactive:
            user_documentation(documentation) # If interactive mode is on, fill in any blanks with user input

        # Create tracklines
        dzt_tracklines = tracklines_by_dzt(sorted_files['.dzt'], documentation, equipment, 1)
        if not dzt_tracklines or len(dzt_tracklines) != len(sorted_files['.dzt']): # .dzt contains most metadata, if all loaded, no need to check other types
            shp_tracklines = tracklines_by_shp(sorted_files['.shp'], documentation, equipment, 1)
        else:
            shp_tracklines = []
        most_valid = max([len(dzt_tracklines), len(shp_tracklines)])
        documentation['trackline_count'] = most_valid

        project_reference_point(documentation, centroids)
        project_locality(documentation)
        default_documentation(documentation) # Finally, fill in any remaining documentation blanks with defaults
        documentation['file_creation'] = datetime.datetime.now(datetime.UTC).date()
        documentation['doc_description'] = f"""File generated via GPR-to-DIGGS conversion script v{version}
Contains references and documentation for all data files for project {documentation['project_name']}"""
        user_equipment(equipment, most_valid)

        # Initialize DIGGS xml
        root = generate_DIGGS_root()
        doc_el = generate_document_info(root, documentation)
        proj_el = generate_project_info(root, documentation, 1) # Only one project per DIGGS file for now
        add_project_refpoint(proj_el, documentation)
        survey_el, files_el = generate_field_survey(root, documentation, 1, 1) # Only one survey per DIGGS file for now

        # Add Tracklines to xml
        no_tracklines = False
        if most_valid > 0:
            if len(dzt_tracklines) == most_valid:
                for trackline in dzt_tracklines:
                    root.append(trackline)
                    add_trackline_id(survey_el, trackline)
            else:
                for trackline in shp_tracklines:
                    root.append(trackline)
                    add_trackline_id(survey_el, trackline)
        else:
            no_tracklines = True
            warnings.warn("No usable tracklines found.")
        proced_el = generate_procedure(survey_el, documentation, equipment)
        if not no_tracklines and proced_el is None:
            raise ValueError("Equipment metadata necessary for proper DIGGS file. Please add properly formatted documentation or answer all questions in interactive mode.")
        survey_timed = add_survey_times(survey_el, documentation) # Dev: Figure out best way to handle lack of survey times

        # Add files to xml
        file_els = generate_file_references(sorted_files['.shp'], "shp", folder_path, 1)
        for file in file_els:
            files_el.append(file)
        file_els = generate_file_references(sorted_files['.dzt'], "dzt", folder_path, 1)
        for file in file_els:
            files_el.append(file)
        file_els = generate_file_references(sorted_files['.grd'], "grd", folder_path, 1)
        for file in file_els:
            files_el.append(file)
        file_els = generate_file_references(sorted_files['.dxf'], "dxf", folder_path, 1)
        for file in file_els:
            files_el.append(file)
        file_els = generate_file_references(doc_text_files, "txt_doc", folder_path, 1)
        for file in file_els:
            files_el.append(file)
        file_els = generate_file_references([f for f in sorted_files['.txt'] if f not in doc_text_files], "txt_other", folder_path, 1)
        for file in file_els:
            files_el.append(file)
        file_els = generate_file_references(gen_fig_files, "image_generated", folder_path, 1)
        for file in file_els:
            files_el.append(file)

        # Associate file extensions with file types
        files_by_type = {'sgy':[], 'pdf':[], 'csv':[], 'image_other':[], 'shp_assoc':[], 'dzt_assoc':[], 'unspecified':[]}
        for file in sorted_files['enveloped']:
            ext = file.suffix.lower()
            if ext == ".sgy":
                files_by_type['sgy'].append(file)
            elif ext == ".pdf":
                files_by_type['pdf'].append(file)
            elif ext == ".csv":
                files_by_type['csv'].append(file)
            elif ext in image_extensions:
                files_by_type['image_other'].append(file)
            elif ext in shp_extensions:
                files_by_type['shp_assoc'].append(file)
            elif ext in dzt_extensions:
                files_by_type['dzt_assoc'].append(file)
            else:
                files_by_type['unspecified'].append(file)

        for key in files_by_type.keys():
            file_els = generate_file_references(files_by_type[key], key, folder_path, 1)
            for file in file_els:
                files_el.append(file)

        # Finish and create xml file
        diggsml_file = folder_path / f"{documentation['project_name'].replace(" ", "_")}.DIGGS.xml"
        with open(diggsml_file, 'w') as oFile:
            oFile.write(ET.tostring(root, pretty_print=True, xml_declaration=True, encoding='utf-8').decode("utf-8"))

        # Package Files into zip directory
        package_files = [f for f in all_files if f not in unsorted_files]
        package_files += [f for f in gen_fig_files if f not in package_files]
        package_files.append(diggsml_file)
        zip_path = folder_path.parent / f"{folder_path.name}.diggs.zip"
        with zipfile.ZipFile(zip_path, "w", compression=zipfile.ZIP_DEFLATED) as zFile:
            for file in package_files:
                zFile.write(file, arcname=file.relative_to(folder_path))

        print(f"Script is finished. Zip file with all packaged files can be found here:\n{zip_path}")

usage = f"python3 {Path(__file__).name} <directory> [-i] [-c] [-p] [-f .extension] [-d] [-h]"
help_message = f"""Script will scan a given directory for matching GPR file types and export them as a DIGGS file. (vers {version})
{usage}
Required Arguments:
<directory>: Folder containing files to process
Optional Arguments:
[-i]: Toggle off interactive mode; minor problems will be handled, major ones will raise an error.
[-c]: Convert to DIGGS format
[-p]: Plot basic figures
[-f .extension]: Set file format for output figures when plotting (must also use -p)
[-d]: Display .dxf file (computationally expensive)
[-h]: Print help message and exit
Supported import file types (others are packaged into zip file):
{" ".join(supported_file_extensions)}
Notes:
-Ensure your directory only contains GPR files for the desired project. Files with matching extensions from other survey types may be mis-represented in output DIGGS file if left in scanned directory.
-Interactive mode is recommended to ensure as thorough documentation as possible in resulting DIGGS file.
"""
if __name__ == "__main__":
    target_dir = None
    convert = False
    plot_figs = False
    fig_ext = ".png"
    display = False
    skip = False
    for i, arg in enumerate(sys.argv):
        if skip:
            skip = False
            continue
        else:
            if Path(arg).is_dir():
                target_dir = Path(arg)
            elif "-h" in arg.lower():
                print(help_message)
                exit()
            elif "-i" in arg.lower():
                interactive = not interactive
            elif "-c" in arg.lower():
                convert = True
            elif "-p" in arg.lower():
                plot_figs = True
            elif "-f" in arg.lower():
                skip = True
                fig_ext = sys.argv[i+1]
            elif "-d" in arg.lower():
                display = True
    if not target_dir:
        print(f"Program requires a target directory to analyze.\n{usage}")
        exit()
    if not convert and not plot_figs:
        print(f"Progam requires an instruction.\n{usage}")
        exit()
    if fig_ext != ".png" and not plot_figs:
        print(f"Must use argument '-p' to plot figures of any format.\n{usage}")
        exit()
    main(target_dir, convert, plot_figs, fig_ext, display)
