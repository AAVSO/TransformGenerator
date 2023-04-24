#
#   TG VERSION 6.9
#
import matplotlib
matplotlib.use('TkAgg')
try:
    import Tkinter
    from Tkinter import *
    import ttk
except ImportError:
    import tkinter
    from tkinter import *
    from tkinter import ttk
try:
    from tkFileDialog import askopenfilenames, asksaveasfile
except ImportError:
    from tkinter.filedialog import askopenfilenames, asksaveasfile
import sys
import numpy as np
from scipy import stats
import matplotlib.pyplot as plt
from matplotlib.pyplot import figure
from time import gmtime,strftime,time
import time
import pickle
#try:
#    from urllib2 import Request,urlopen
#    from urllib2.error import URLError
#except ImportError:
#    from urllib.request import Request, urlopen
#    from urllib.error import URLError
import ssl
import urllib.request
from urllib.request import urlopen

from pylab import get_current_fig_manager
import json
from decimal import *
#############################################################################################
#############################################################################################
#                                                                                           #
#   Photometry transformation coefficients program                                          #
#                                                                                           #
#       This program calculates the two-color filter magnitude transformation               #
#       coefficients described in Henden - "Astronomical Photometry" and                    #
#       Bruce Gary's "CCD TRANSFORMATION EQUATIONS FOR USE WITH SINGLE IMAGE                #
#       (DIFFERENTIAL) PHOTOMETRY".
#
#      Version 6.9
#              add single filter photometry creation of Tv_bv
#      Version 6.8 (no release version 6.7)
#              Remove security test for AAVSO website
#              Expand window to display saved transform sets
#              Updated pickradius to new standard
#              Increase figsize of plots
#
#      Version 6.6 (no version 6.5 created)
#              Add support for additional transform coefficients for Lesve (Tbr,Tbi,Tb_br,Tb_bi)
#              Add new VPhot format option (new Max column) 
#      
#      Versionn 6.4
#              Add support for Landolt field
#              Fix delete transform sets (Mac issue)
#      Version 6.3
#              Add Melotte 111 field support
#              Add code to import and work on both Python 3.x and 2.7 
#      Version 6.#0  
#              Rename of Veresion 5.12 beta for release
#      Version 5.12 beta
#                  Correct bright star VSP label issue with underscore xx_
#      Version 5.11a_beta
#                  Correct problem if mix of valid and bad instrument magnitude measurements
#      Version 5.11 beta
#                  Correct Errormsg on TG input when no stars missing
#                  M67 original Henden star 45 cross reference removed 
#                      - star no longer in reference field
#                  Add NGC 3532 support
#                  Add NGC 1252 support
#      Version 5.10
#                  Chanage original lines to all measurements lines
#      Version 5.9 beta 
#                  Add M11 Standard field
#                  Change plot of sigma lines to show y_sigma not slope error
#
#      Version 5.8
#                  Change VSP link to new VSP API (retrieves standard reference mags)
#      Version 5.7
#                  Mac terminal required change to max screen size
#                  Fix delete saved transforms - apparent change in Python str
#                  Add error message on no files selected to average
#                  Increase max number of allowed VPHOT comps to 500 minus Boulder ids
#      Version 5.6
#                  Error Correction on star selection plot
#
#      Version 5.5
#                  Rename program to TransformGenerator_V5.5
#      Version 5.4a beta
#                  add scroll bars to main menus
#                  add fixed original 3 sigma lines plus updating 3 sigma line on plot
#                  fix plotting range error caused by bad star measurements
#
#      Version 5.3 
#                  change two three sigma error lines on plot
#      Version 5.2 beta
#                  prevent JD= "" from causing a display problem
#                  add one sigma lines to plots
#
#      Version 5.1
#                  change VPHOT error message format on stars not in VSP
#                  change M67 target id to hn cnc
#                  change VSP standards request to fov of 60, not 30
#
#      Version 5.0 formal release of new version
#      
#      Version 4.9
#                  fix for Mac reading blank VPHOT lines as /r/n, not /n
#                  changed way matplotlib closes open figure - still doesn't fix mac problem
#                  modify alignment of transform set data on main menu
#
#      Version 4.8
#                  add delete old transform
#                  caption change from observation sets to transform set
#                  prepare to send out as a 5.0 beta test version
#
#      Version 4.7 beta-a
#                  Add SNR threshold on which comps to use
#
#      Version 4.7 beta
#                 add error message for star id's in instrument file not in standards
#                 add VPHOT interface
#
#      Version 4.6
#                 Retrieve standard reference stars from VSP
#
#      Version 4.5 
#                 Add Maxim input format for instrument magnitudes
#
#      Version 4.4
#                 change max number of star instrument measurement lines from 100 to 300
#                 allow 300 reference stars
#                 allow 300 star measurements
#                 allow star ids to be text 
#
#
#      Version 4.3
#                 change export transform file format to ini file for TA input
#
#      Version 4.2
#                 add transform error and r^2 values
#                 change export file to .ini file matching TA input requirements
#                 allow mulitple values for each filter on star instrument measurement lines
#                 
#
#      Version 4.1
#                 fix allowing no delimiter at end of Filt line
#                 change transform nominclature to AAVSO standard
#                 
#      Version 4.0
#                add V-I transforms
#      Version 3.8 - save computed averages to config_data file also - for future use
#                     add file name to message on avg transform export file
#                     clears transform values when new file selected
#                     fix to file name overlay bug
#                     add standards field name to display of observation sets
#
#      Version 3.7 
#               turn interactive matplotlib OFF - (on Mac, default is on...)
#               Add export of averaged transforms
#
#
#      Version 3.6
#               Clearing plot on each select, changing color of previous line
#
#
#      Version 3.5 eliminated multiple select_lines texts
#
#
#      Version 3.4 April 4, 2014
#                modified structure to remove recursion problem and incorporate draw()      #
#
#       Version 3.3 April 3, 2014
#                   Changes : Plot mods to work on MAC
#             Version 3.2  April 2, 2014                                                          #
#                   Changes :  Tix dependency removed, minor menu format changes            #
#                                                                                           #
#       This program is currently undergoing new development.  Contact Gordon Myers at      #
#         gordonmyers@hotmail.com                                                           #
#                                                                                           #
#############################################################################################
#############################################################################################




#############################################################################################
#                                                                                           #
#  calculatetransforms() is initiated after the user has loaded the measurements            #
#  file, standard field stars are loaded, and the user selects "Calculate Transforms"       #
#  on the primary Transform Window.               -                                         #
#       Using data previously entered - telescope name, standard reference field id and     #
#                  file containing measurement data, this method -                          #
#                                                                                           #
#          - standard field data is loaded  (Henden M67, NGC 7790, ...                      #
#          - 'md' (magnitude difference) array is created with all measurements needed      #
#            for calculations - e.g. b-v, v-r, U-B, etc.  (upper case letters are standard  #
#            field reference magnitude, lower case are telescope machine magnitudes)        #
#          - transform_calc method is queued whih uses a least squares routine to compute   #
#            the transformation coeffients                                                  #
#          - transformation coefficients are displayed on screen with selectable tie        #
#            to interactive plot for further analysis                                       #
#          - transformation coefficients are saved to disk                                  #
#                                                                                           #
#############################################################################################
def calculatetransforms():
            global md_col_list,meas_JD,transform_names,transform_inst,num_meas_stars,transform_raw_data,fig1,tel_id,meas_JD
            global txtboxlab,titlab,std_field_name,transform_val_err,star_id_list,file_namelist,vphot_snr,radecwindow,enteredfield

           
#
# Create transforms from instrument magnitude measurement data
#
            telescopename = tel_id # Telescope Name
            std_field_name = var.get()
#
#   Retrieve Standards file from ASP VSP
#
            if std_field_name == "M67":
                searchfield = "ra=132.825&dec=11.8"
            elif std_field_name == "NGC7790":
                searchfield = "ra=359.6&dec=61.217"
            elif std_field_name == "M11":
                searchfield = "ra=282.775&dec=-6.267"
            elif std_field_name == "NGC 1252":
                searchfield = "ra=47.704&dec=-57.767"
            elif std_field_name == "NGC 3532":
                searchfield = "ra=166.412&dec=-58.752"
            elif std_field_name == "Melotte 111":
                searchfield = "ra=186.275&dec=26.1"
            elif std_field_name == "Landolt Field": # Search input file for RA/Dec
# Open input file (if AIP4WIN, the only file; if VPHOT first of multiple - only look at first file for RA/Dec)
                searchra,searchdec = "Landolt","Landolt" # set as default in case no RA/Dec found
                try:
                    measurements = open(magfilenam,mode="r")  # retrieve instrument measurements file
                except:
                    Errormsg("Invalid File Name - '"+magfilenam+"'")
                    return
#  Use selected format to decide how to search for RA/Dec
                if fmt_name.get() == "VPHOT":  # check if instrument magnitudes are in VPHOT
# Process one VPHOT file to find RA/DEC  
  
                    for oneline in measurements: # process each line in the file
#                        print("oneline in measurements - ",oneline)
                        if oneline == "\n" or oneline == "\r\n":
                            continue # read next line
                        aline = [] # create holding list for parsed oneline
                        delim = [":",":"]  # colon delimeter
                        lineparse(oneline,aline,delim)
                        if aline[0] == "R.A.":
                            searchra = str(15*(float(aline[1])+float(aline[2])/60+float(aline[3])/3600))[:7]
                        if aline[0] == "Dec.":
                            searchdec = str(np.sign(float(aline[1]))*(abs(float(aline[1]))+float(aline[2])/60+float(aline[3])/3600))[:6]
                        if searchra != "Landolt" and searchdec != "Landolt" :
                            break  #  found ra and dec - 
# Process AIP4WIN, TG or MaxIm file
                else:  #  Landolt input file must be TG/AIP4WIN or MaxIm
                    for oneline in measurements: # process each line in the file
                        if oneline.find("Target") == -1:
                            continue  # not target line - go to next line
                        i = oneline.find("RA=")
                        if i > 0:  # RA found
                            j = oneline.find(" ",i) # find spaace after RA
                            searchra = oneline[i+3:j]
                        i = oneline.find("DEC=")
                        if i > 0:  #DEC found
                            j = oneline.find(" ",i)  # find space after DEC
                            searchdec = oneline[i+4:j]
                        if searchra != "Landolt" and searchdec != "Landolt":
                                break # found ra and dec 
                if searchra == "Landolt" or searchdec == "Landolt":  # if ra/dec not found, request manual entry
                    ra_dec_entry_window() # Display Window to obtain RA/Dec from user
                    root.wait_window(radecwindow)
                    searchfield = enteredfield  #  use values entered by user
                    print("searchfield ",searchfield)
                else:
                    searchfield = "ra=" + searchra + "&dec=" + searchdec  # use values from instrument files
#  Change "Landolt Field" standard field name to more specific value
                k = searchfield.find("&")
                m = searchfield.find(".",k+5)
                if m == -1 :  # no period
                    m = len(searchfield)
                if searchfield[k+5:k+6] == "-" :
                    dec = searchfield[k+6:m]
                    if len(dec)  == 1:
                        dec = "0" + dec
                    dec = "-" + dec
                else:
                    dec = searchfield[k+5:m]
                    if len(dec) == 1:
                        dec = "0" + dec
                    dec = "+" + dec
                ra = str(((float(searchfield[3:k]))/15) + .05)[:4]  # round ra to nearest tenth of an hour
                if ra[1:2] == ".":
                    ra = "0" + ra[0:3]
                
                std_field_name = "LF " + ra + dec
#                print ("searchfield ",searchfield)
                    
                    
                    
            else:
                print("Should not get here!")
                        
            
# Retrieve Standard Field File 
          
            star_id_list = [] # start list of reference star ids - will contain AUID or Boulder ids
            star_id_list_label = [] # start matching list to contain VPHOT/VSP label (duplicates at times...)
            sf_col_list = ["RA","Dec","U","B","V","R","I"] # list names of each column in std_field_mags array
# Create Master Standard Field Magnitudes array
            std_field_mags = np.zeros((500,len(sf_col_list))) # allow 500 reference stars

##############################################################################################
            ##################################################################################
############
##              NEW VSP API CODE TO RETIEVE STANDARD REFERENCE MAGNITUDES
#a
            try:
               
                ctx = ssl.create_default_context()
                ctx.check_hostname = False
                ctx.verify_mode = ssl.CERT_NONE
                f = urlopen('https://app.aavso.org/vsp/api/chart/?'+ searchfield +'&fov=179&maglimit=16.5&special=std_field&format=json',context=ctx)
                
                
            except urllib.error.URLError as e:
                print("TG error information")
                print("Line of code causing error - f = urlopen('https://app.aavso.org/vsp/api/chart/?'+ searchfield +'&fov=210&maglimit=16.5&special=std_field&format=json'")
                print("error information = ",e),
                print("searchfield = " + searchfield)
                Errormsg("Could Not Access AAVSO Web Site")
                return
            chart_data = json.load(f)   # chart_data is a python dictionary
            vsp_ref_data = chart_data.get("photometry")  # vsp_ref_data is a Python list, vsp_ref_data[i] are dictionaries
            i = 0 # avoid error if no reference stars
            for i in range(len(vsp_ref_data)):
                star_id_list.append(vsp_ref_data[i].get("auid"))  # store auid
                star_id_list_label.append(str(vsp_ref_data[i].get("label")))  # store VPHOT/VSP label - use string format to match AIP and MaxIm
#  Get, convert and save right ascension
                line = vsp_ref_data[i].get("ra")  # set up ra parse
                delim = [":",":"]  #  set colon parse delimeter
                aline = []
                lineparse(line,aline,delim)  # parse line
                std_field_mags[i,0] = (Decimal(aline[0]) + Decimal(aline[1])/Decimal('60') + Decimal(aline[2])/Decimal(3600))*Decimal(15)  # ref star right ascension in degrees
#                print("RA - line,aline,std_field_mags[i,0]",line,aline,std_field_mags[i,0])
#  Get, convert and save declination
                line = vsp_ref_data[i].get("dec")  # set up declination parse
                aline = []
                lineparse(line,aline,delim)
                std_field_mags[i,1] = Decimal(aline[0]) + Decimal(aline[1])/Decimal(60) + Decimal(aline[2])/Decimal(3600)
#                print("Dec - line,aline,std_field_mags[i,1]",line,aline,std_field_mags[i,1])
#  Get and save standard star reference magnitudes     
                band_meas = vsp_ref_data[i].get("bands")  # get list of photometry reference values - each entry is a dictionary
                bandmapping = ["","","U","B","V","Rc","Ic"]  # .index will provide index for std_field_mags
                std_field_mags[i,bandmapping.index("U")] = -1000 # set to no data in case no U value provided
                for j in range(len(band_meas)):
                    if band_meas[j].get("band") in bandmapping:  # look out for new bands being added
                        std_field_mags[i,bandmapping.index(band_meas[j].get("band"))] = band_meas[j].get("mag")
                
                
            std_field_star_count = i + 1
            if std_field_star_count < 3 :
                Errormsg("Less than 3 Reference Stars - Abort Calculations")
                return            
            
#
#  For NGC7790 and M67, add original Henden star identifiers to master standard field magnitudes array - but use current VSP reference magnitudes
#
            if std_field_name == "M67":
                star_id_add_list = m67_AUID_map
            elif std_field_name == "NGC7790":
                star_id_add_list = ngc7790_AUID_map
            else:
                star_id_add_list = []  # No stars to add
            j = -1 # keep count of star ids added
            for i in range(len(star_id_add_list)):  # for each star in original list, add line to std_field_mags array and star_id_list list if matching AUID
                try:  # check if original star id has current day AUID
                    match_AUID_index = star_id_list.index(star_id_add_list[i][1])
                    j = j+1 # keep count of star ids being added (actually index starting with zero)
                    star_id_list.append(str(star_id_add_list[i][0])) # append old star id to star id list
                    std_field_mags[std_field_star_count+j,] = std_field_mags[match_AUID_index,]  # copy current VSP values for the star
                    star_id_list_label.append(star_id_list_label[match_AUID_index])
                    
                except:
                    dummy = 0 # for now, don't do anything
    #                Errormsg("Original star id " + str(star_id_add_list[i][0]) + " no longer valid reference star - star measurements will be skipped")
            
            std_field_star_count = std_field_star_count + j
#
#            for m in range(std_field_star_count):
#                print("m,star_id_list[m],star_id_list_label[m],std_field_mags[m,]",m,star_id_list[m],star_id_list_label[m],std_field_mags[m,])
                
                
#:
            
#  Reference file of standard stars to use created - star_id_list and std_field_mags
#
#
#######################################################################################################################################
#
#       Start processing of instrument machine magnitude files
#
#######################################################################################################################################
# Read format indicator and then instrument Machine Magnitudes file, then format in consistent array
            try:
                  measurements = open(magfilenam,mode="r")  # retrieve instrument measurements file
            except:
                  Errormsg("Invalid File Name - '"+magfilenam+"'")
                  return
            
            measured_machine_mags = np.zeros((500,8)) # Create array for measured machine magnnitudes
            mmm_col_lst = ["Star_id_index","RA","Dec","u","b","v","r","i"]
            u_ind,b_ind,v_ind,r_ind,i_ind = 0,0,0,0,0  #  Set filter used indicators to zero
            meas_JD = str(100000)  # indicate no date in file data
# Read format indicator
            
            if fmt_name.get() == "TG / AIP4WIN":  # check if instrument magnitudes are in TG / AIP4WIN format - if so,  
############################################################################################################################
#
# ________________________ Start Processing instrument magnitudes for TG format and store in measured_machine_mags
#
############################################################################################################################
                
                
                if(len(file_namelist) != 1):
                    Errormsg("Only one file allowed for TG / AIP4WIN Processing")
                    return
                num_meas_stars = 0 # initialize count of number of measurements lines of stars
                filt_line = "N" # indicate no Filt line in file yet read
                star_id_not_matched_list = "" # start list of star id's not matched
                for oneline in measurements:  # Search for Filt in first column
                    aline = [] # create holding list for parsed oneline
                    delim = [";",","]  # allow two delimeters
                    lineparse(oneline,aline,delim)
                    if len(aline) == 0: # see if any fields in line
                        aline.append("dummy")  # if no content make next set of ifs ignore line                
                    if aline[0] == "Julian_Day":
                        meas_JD = aline[1]
                    if aline[0] == "Filt": # if yes, create list of column labels
                        column_names = aline
                        filt_line = "Y"  # indicate Filt line found in data file
                        save_column_labels_line = oneline
# Find columns with machine magnitudes
                        ucol=[]
                        bcol=[]
                        vcol=[]
                        rcol=[]
                        icol=[]
                        for j in range(len(column_names)):
                            tcol = column_names[j].lower()
                            if tcol == "u":
                                ucol.append(j) # add column number to list - allows multiple values for same filter
                                u_ind = 1 # indicate u filter images taken
                            elif tcol == "b":
                                bcol.append(j)
                                b_ind = 1 # indicate b filter images taken
                            elif tcol == "v":
                                vcol.append(j)
                                v_ind = 1
                            elif tcol == "r":
                                rcol.append(j)
                                r_ind = 1
                            elif tcol == "i":
                                icol.append(j)
                                i_ind = 1
                        
# Read measured machine magnitudes and store in measured_field_mags
                    try:
                        star_id_index_num = star_id_list.index(aline[0]) # See if first field contains a reference star id and get index number of match
                        if filt_line == "N": # If yes, check that Filt line was found first
                            Errormsg("No 'Filt' line found in file prior to star measurements")
                            break
# Valid magnitude measurement line found - start processing
                        srow = num_meas_stars
                        
                        measured_machine_mags[srow,mmm_col_lst.index("Star_id_index")] = star_id_index_num # Star id index number
                        
            
                        num_meas_stars = num_meas_stars + 1 # count number of measuremnent lines
                        if len(ucol) != 0: # Verify u measurements provided
                            temp = []
                            for k in range(len(ucol)):
                                try:
                                    temp1 = float(aline[ucol[k]])
                                    temp.append(temp1) # create list of all u measurements watching out for error msg measurements like "bad"
                                except:
                                    dummy=0 # do nothing
                            if len(temp) != 0:
                                measured_machine_mags[srow,3] = np.mean(temp) # u averagge magnitude
                            else:
                                measured_machine_mags[srow,3] = -1000 # Set no valid measurement indicator
                            
                        if len(bcol) != 0:
                            temp = []
                            for k in range(len(bcol)):
                                try:
                                    temp1 = float(aline[bcol[k]])
                                    temp.append(temp1) # create list of all b measurements
                                except:
                                    dummy=0 # do nothing
                            if len(temp) != 0:
                                measured_machine_mags[srow,4] = np.mean(temp) # b averagge magnitude
                            else:
                                measured_machine_mags[srow,4] = -1000 # Set no valid measurement indicator
                               
                        if len(vcol) != 0:
                            temp = []
                            for k in range(len(vcol)):
                                try:
                                    temp1 = float(aline[vcol[k]])
                                    temp.append(temp1) # create list of all v measurements
                                except:
                                    dummy=0 # do nothing
                            if len(temp) != 0:
                                measured_machine_mags[srow,5] = np.mean(temp) # v averagge magnitude
                            else:
                                measured_machine_mags[srow,5] = -1000 # Set no valid measurement indicator
                                                      
                        if len(rcol) != 0:
                            temp = []
                            for k in range(len(rcol)):
                                try:
                                    temp1 = float(aline[rcol[k]])
                                    temp.append(temp1) # create list of all r measurements
                                except:
                                    dummy=0 # do nothing
                            if len(temp) != 0:
                                measured_machine_mags[srow,6] = np.mean(temp) # r averagge magnitude
                            else:
                                measured_machine_mags[srow,6] = -1000 # Set no valid measurement indicator
                                
                        if len(icol) != 0:
                            temp = []
                            for k in range(len(icol)):
                                try:
                                    temp1 = float(aline[icol[k]])
                                    temp.append(temp1) # create list of all i measurements
                                except:
                                    dummy=0 # do nothing
                            if len(temp) != 0:
                                measured_machine_mags[srow,7] = np.mean(temp) # i averagge magnitude
                            else:
                                measured_machine_mags[srow,7] = -1000 # Set no valid measurement indicator
                        
                    except:  # Get here for non star id matched lines - 
                        if (aline[0][3:4] == "-" and aline[0][7:8] == "-") or aline[0].isdigit(): # check for valid star id
                            star_id_not_matched_list = star_id_not_matched_list + aline[0]+"\n"  # add id to list of names for error message
                if star_id_not_matched_list != "":
                    Errormsg("Reference Star ids not found in VSP -\n" + star_id_not_matched_list + "\nStars excluded from calculation")
                            
                        
                        

                
         
#______________________________________  End of Code Reading TG / AIP4WIN instrument magnitudes and storing in measured_machine_mags file__________
#
############################################################################################################################
#
# ________________________ Start Processing instrument magnitudes for MaxIM format and store in measured_machine_mags
#
#  measured_machine_mags = np.zeros((300,8)) 
#           mmm_col_lst = ["Star_id_index","RA","Dec","u","b","v","r","i"] of second index - first index of measured_machine_mags is internal measurement number
#            
#############################################################################################################################


            elif fmt_name.get() == "MaxIm":
                
                if(len(file_namelist) != 1):
                    Errormsg("Only one file allowed for MaxIm Processing")
                    return
                star_id_not_matched_list = [] # start list of any reference stars not in VSP data
                line_num = 0
                filt_used_maxim = [] # initialize list of filters found in MaxIm instrument mag file
                filter_image_count = [0, 0, 0, 0, 0] # for tracking how many lines are input for each filter
                filter_allowed = ["u", "b", "v", "r", "i"] # for indexing the above line count 
                for oneline in measurements:  # Process each line in file
                    line_num = line_num + 1
                    aline = [] # create holding list for parsed oneline
                    delim = [";",","]  # allow two delimeters
                    lineparse(oneline,aline,delim)
                    if line_num == 1:  #process first line
                        if aline[0].strip() != "Timestamp (JD)" or aline[1].strip() != "Filter":
                            Errormsg("Invalid MaxIm file format")
                            return
                        else: #Process first header line finding star ids and column numbers
                            num_cols = len(aline) # number of columns
                            col_with_im = [] # start list of columns with instrument magnitudes
                            col_star_id = [] # start list of star ids for each column
                            for i in range (2,num_cols):
                                if aline[i][-33:] == ": Instrument Magnitude (Centroid)":
                                    col_with_im.append(i)
                                    col_star_id.append(aline[i][:-33].strip())
                    else: # Process lines after line 1 - all assumed to be measurement lines
                        meas_JD = aline[0] # use time measurement for display of times for transform - assumes images taken close to same time
                        temp = aline[1].strip() # identify filter used in line
                        temp = temp.lower()
                        filter_image_count[filter_allowed.index(temp)] += 1  
                        k = 0 # start count of measured stars that are in VSP list
                        for j in range(len(col_with_im)):  # j is internal column measurement number
                            try:
                                measured_machine_mags[k,0] = star_id_list.index(col_star_id[j]) #store star id index
                                measured_machine_mags[k,mmm_col_lst.index(temp)] = (measured_machine_mags[k,mmm_col_lst.index(temp)]*(filter_image_count[filter_allowed.index(temp)] - 1) + float(aline[col_with_im[j]]))/ filter_image_count[filter_allowed.index(temp)] # average in latest measurement and store filter instrument magnnitude
                                k = k +1  # bump index for next star                                )
                            except:  # Get here for non star id matched columns -
                                
                                if len(star_id_not_matched_list) == 0:
                                    star_id_not_matched_list.append(col_star_id[j])  # add initial id to list of names not found in VSP for error message
                                else:  # add to list if not already there
                                    already_listed = 0
                                    for m in range(len(star_id_not_matched_list)):
                                        if star_id_not_matched_list[m] == col_star_id[j]:
                                            already_listed = 1
                                    if already_listed == 0:
                                        star_id_not_matched_list.append(col_star_id[j])
                message = ""
                if len(star_id_not_matched_list) != 0:
                    for m in range(len(star_id_not_matched_list)):
                        message = message + star_id_not_matched_list[m] + "\n"
                    Errormsg("Reference Star ids not found in VSP -\n" + message +"\nStars excluded from calculation")
                                
                if filter_image_count[filter_allowed.index("u")] > 0:
                    u_ind = 1  # indicate u filter data
                if filter_image_count[filter_allowed.index("b")] > 0:
                    b_ind = 1  # indicate b filter data
                if filter_image_count[filter_allowed.index("v")] > 0:
                    v_ind = 1  # indicate v filter data
                if filter_image_count[filter_allowed.index("r")] > 0:
                    r_ind = 1  # indicate r filter data
                if filter_image_count[filter_allowed.index("i")] > 0:
                    i_ind = 1  # indicate i filter data
                num_meas_stars = k-1

################################################################################################################
#
#    Process VPHOT format instrument magnitude files
# 
################################################################################################################
                
            elif fmt_name.get() == "VPHOT":
#                print("star_id_list_label,star_id_list",star_id_list_label,star_id_list)
#                if len(file_namelist) < 2 :  CODE REMOVED TO ALLOW SINGLE FILTER TRANSFORMS
#
#                   Errormsg("Need at least two filters data to create transforms")
#                    return
# Read and process first VPHOT file
                snr_limit = float(vphot_snr.get())
                vphot_filt_list = []
                vphot_star_id = []
                for i in range(500):  # nax number of vphot comps allowed is 500 minus the number of old Boulder ids - added later
                    vphot_star_id.append(" ")    # create array with vphot id's tied to AUID  (star_id_list)
                mmm_obs_count_col_list = ["Star_id_index","u","b","v","r","i"]
                mmm_obs_count = np.zeros((500,len(mmm_obs_count_col_list))) # Create array to count number of measurements for each filter - for averaging
                srow = 0 # initialize index of last row with valid data in measured_machine_mags array
                star_id_not_matched_list = "" 
                one_msg_line = ""
                mmm_data_started = "N"                
                for file_i in range(len(file_namelist)): # process each file listed
                    measurements = open(file_namelist[file_i],mode="r")  # retrieve instrument measurements file
  #                  print('measurements line 669 V6.9 =',measurements)
                    
                    starline_found = "N"
                    activestars = 0 # set to count active stars to ensure some found 
                    for oneline in measurements: # process each line in the file
 #                       print("oneline in measurements - ",oneline)
                        if oneline == "\n" or oneline == "\r\n":
                            continue # read next line
                        aline = [] # create holding list for parsed oneline
                        delim = ["\t","\t"]  # tab delimeter
                        lineparse(oneline,aline,delim)
                        if starline_found == "N": #process header lines
                            if aline[0][:7] == "Filter:":  # find Filter line
                                currentfilter = aline[0][8:9].lower()
                                if currentfilter == "u":
                                    u_ind = 1
                                elif currentfilter == "b":
                                    b_ind = 1
                                elif currentfilter == "v":
                                    v_ind = 1
                                elif currentfilter == "r":
                                    r_ind = 1
                                elif currentfilter == "i":
                                    i_ind = 1
                                else:
                                    Errormsg("File " + file_namelist[file_i] + "\n contains invalid filter name " + aline[0][8:len(oneline)] + "\n File Skipped")
                                    break
                                continue
                            if aline[0][:3] == "JD:":  #Find Julian Date
                                meas_JD = aline[0][4:]
                                continue
                                
                            if aline[0] == "Star": # Found line ahead of measurement data - set to process measurement lines
                                vphot_col_list = []
                                aline[0] = "Vphot_Star_id" # clarify this is a VPhot star id
                                for count in range(len(aline)):
                                    if aline[count][-4:] == "-mag":
                                        aline[count] = "Ref-mag"  # allow single referce
                                    
                                    vphot_col_list.append(aline[count])                                    
#                                    print("count, value ", count, aline[count])
                                starline_found = "Y"
#                                print("vphot_col_list",vphot_col_list)
                                
                            
                            continue  # done looking at header lines - most ignored
#p
# Start processing lines of measurement data following "Star" line
#
                        else:
                            # process measurement lines - separate logic for AUID vs VPhot id
 #                           print("starts Star line process - aline",aline)
                            if(aline[0][:4] == "000-") :  # process AUID
                                j = star_id_list.index(aline[0])
                                vphot_AUID_index = j
                                vphot_star_id[j] = aline[0]
                            else: # process VPhot ids
                            
                                label = aline[0][:3] # get first 3 numbers of vphot_star_id - should match VSP label - also works for two digit star_id
                                if label[-1:] == "_": #remove underscore if two digit star id 
                                    label = label[:-1]
                                try:
                                    
                                    ref_star_id_line_label_match_index = star_id_list_label.index(label)
                                    
                                except:
                                    if (aline[0][3:4] == "-" and aline[0][7:8] == "-") or aline[0].isdigit(): # check for valid star id
                                        one_msg_line = one_msg_line + aline[0] + ", " # add id to list of names
                                        if len(one_msg_line) > 30:
                                            star_id_not_matched_list = star_id_not_matched_list + one_msg_line + "\n"  # add line to error message
                                            one_msg_line = ""
                                    continue # no match - go to next measurement file input line
     #                           print("V6.9 line 734 ref_star_id_line_label_match_index is ",ref_star_id_line_label_match_index)
        # Search VSP data with same label to find matching star magnitude and B-V # sf_col_list = ["RA","Dec","U","B","V","R","I"] # list names of each column in std_field_mags array  ;
                                for j in range(ref_star_id_line_label_match_index,ref_star_id_line_label_match_index + 20):
                                    if abs(float(aline[vphot_col_list.index("Ref-mag")]) - std_field_mags[j,sf_col_list.index(currentfilter.upper())]) < .001 and \
                                       abs(float(aline[vphot_col_list.index("B-V")]) - ((std_field_mags[j,sf_col_list.index("B")] - std_field_mags[j,sf_col_list.index("V")]))) < .001:
                                         vphot_AUID_index = j
                                         vphot_star_id[j] = aline[vphot_col_list.index("Vphot_Star_id")] # save VPHOT Star id
                                     
#
#               AUID of VPHOT measurment known, save measurement in measured_machine_mags array - find out if found before and set measurement row number
                            if mmm_data_started == "Y": # any data yet stored 
                                
                                
                                for m in range(srow + 1): # search if vphot_AUID_index already stored
                                    if vphot_AUID_index == measured_machine_mags[m,mmm_col_lst.index("Star_id_index")]: # if match, set instrument row number
                                        break
                                k = m  # set k to store data in matching row, but...
                                
                                if (m == srow and vphot_AUID_index != measured_machine_mags[srow,mmm_col_lst.index("Star_id_index")]): # if last entry also not match, start new row
                                    srow = srow +1 # add new measurement row - srow is size of array data
                                    k = srow # target new row to store data
                                    
                            else:
                                k = 0  # if no entries, make this the first
                                mmm_data_started = "Y"
                                
                                    
                              
                            measured_machine_mags[k,mmm_col_lst.index("Star_id_index")] = vphot_AUID_index # add new id
                            mmm_obs_count[k,mmm_obs_count_col_list.index("Star_id_index")] = vphot_AUID_index
                            temp = aline[vphot_col_list.index("SNR")]
                            if temp.isdigit() is False: # watch out for VPHOT blank in place of comma...
                                blank_at = temp.find(" ")
                                aline[vphot_col_list.index("SNR")] = temp[:blank_at] + temp[blank_at + 1:len(temp)]
                                                                              
                            if aline[vphot_col_list.index("Active")] == "True" and float(aline[vphot_col_list.index("SNR")]) > snr_limit: # check for invalid measurement
                                activestars += 1 # count VPhot active stars matched
                                measured_machine_mags[k,mmm_col_lst.index(currentfilter.lower())] = (mmm_obs_count[k,mmm_obs_count_col_list.index(currentfilter)]* \
                                                                                             measured_machine_mags[k,mmm_col_lst.index(currentfilter)] + \
                                                                                             float(aline[vphot_col_list.index("IM")]))/   \
                                                                                             (mmm_obs_count[k,mmm_obs_count_col_list.index(currentfilter)] + 1)
                                
                                mmm_obs_count[k,mmm_obs_count_col_list.index(currentfilter)] += 1 # add one to count of observations for this filter
                            else:
                                if mmm_obs_count[k,mmm_obs_count_col_list.index(currentfilter)] == 0: # if no valid data for this filter, indicate bad data found
                                    measured_machine_mags[k,mmm_col_lst.index(currentfilter.lower())] = -1000 # set bad data indicator
                                
                
                if star_id_not_matched_list != "":
                    Errormsg("Reference Star ids not found in VSP -\n" + star_id_not_matched_list + one_msg_line + "\nStars Excluded from Calculation")
                if activestars < 2:
                    Errormsg("Less than two active stars in VPhot File")
                    return
                num_meas_stars = srow + 1 # total number of stars with measurements
#
# Search all magnnitudes and set any 0 to -1000 indicating no measurement or bad measurement
# mmm_col_lst = ["Star_id_index","RA","Dec","u","b","v","r","i"]
#
                for i in range(num_meas_stars):
                    for j in range(3,8):
                        if measured_machine_mags[i,j] == 0:
                            measured_machine_mags[i,j] = -1000


                
                     
                                    

        
                                 
 
########################################################################################################
#
# Create Array of Various Magnitude Differences for Transform Calculation - md== magnitude difference
#
########################################################################################################
# Print data for review of bad data

#            print("AUID        u          b              v                 r                 i")    
#            for i in range(num_meas_stars):
#                idnum = int(measured_machine_mags[i,mmm_col_lst.index("Star_id_index")])
#                print(star_id_list[idnum],measured_machine_mags[i,mmm_col_lst.index('u')],measured_machine_mags[i,mmm_col_lst.index('b')],measured_machine_mags[i,mmm_col_lst.index('v')], \
#                               measured_machine_mags[i,mmm_col_lst.index('r')],measured_machine_mags[i,mmm_col_lst.index('i')])
                

            if num_meas_stars <2:
                Errormsg("No valid reference data to compute transforms")
                return
            md_col_list = ["Star_id_index","RA","Dec","U-B","B-V","B-R","B-I","V-R","R-I","U-u","B-b","V-v","R-r","I-i","u-b","b-v","b-r","b-i","v-r","r-i","V-I","v-i"]
            md = np.zeros((num_meas_stars,len(md_col_list))) # magnitude differences array
            for i in range(num_meas_stars):
                md[i,md_col_list.index("Star_id_index")] = measured_machine_mags[i,mmm_col_lst.index("Star_id_index")] # Star id index number
                j = int(md[i,md_col_list.index("Star_id_index")])  # Star id index number
                md[i,md_col_list.index("RA")] = std_field_mags[j,sf_col_list.index("RA")]
                md[i,md_col_list.index("Dec")] = std_field_mags[j,sf_col_list.index("Dec")]
                md[i,md_col_list.index("U-B")] = std_field_mags[j,sf_col_list.index("U")] - std_field_mags[j,sf_col_list.index("B")]
                md[i,md_col_list.index("B-V")] = std_field_mags[j,sf_col_list.index("B")] - std_field_mags[j,sf_col_list.index("V")]
                md[i,md_col_list.index("B-R")] = std_field_mags[j,sf_col_list.index("B")] - std_field_mags[j,sf_col_list.index("R")]
                md[i,md_col_list.index("B-I")] = std_field_mags[j,sf_col_list.index("B")] - std_field_mags[j,sf_col_list.index("I")]
                md[i,md_col_list.index("V-R")] = std_field_mags[j,sf_col_list.index("V")] - std_field_mags[j,sf_col_list.index("R")]
                md[i,md_col_list.index("R-I")] = std_field_mags[j,sf_col_list.index("R")] - std_field_mags[j,sf_col_list.index("I")]
                md[i,md_col_list.index("V-I")] = std_field_mags[j,sf_col_list.index("V")] - std_field_mags[j,sf_col_list.index("I")]
                md[i,md_col_list.index("U-u")] = std_field_mags[j,sf_col_list.index("U")] - measured_machine_mags[i,mmm_col_lst.index("u")]
                md[i,md_col_list.index("B-b")] = std_field_mags[j,sf_col_list.index("B")] - measured_machine_mags[i,mmm_col_lst.index("b")]
                md[i,md_col_list.index("V-v")] = std_field_mags[j,sf_col_list.index("V")] - measured_machine_mags[i,mmm_col_lst.index("v")]
                md[i,md_col_list.index("R-r")] = std_field_mags[j,sf_col_list.index("R")] - measured_machine_mags[i,mmm_col_lst.index("r")]
                md[i,md_col_list.index("I-i")] = std_field_mags[j,sf_col_list.index("I")] - measured_machine_mags[i,mmm_col_lst.index("i")]
                md[i,md_col_list.index("u-b")] = measured_machine_mags[i,mmm_col_lst.index("u")] - measured_machine_mags[i,mmm_col_lst.index("b")]
                if md[i,md_col_list.index("u-b")] == 0:
                    md[i,md_col_list.index("u-b")] = -1000  # indicate from bad measurments - e.g. both values set to -1000
                md[i,md_col_list.index("b-v")] = measured_machine_mags[i,mmm_col_lst.index("b")] - measured_machine_mags[i,mmm_col_lst.index("v")]
                if md[i,md_col_list.index("b-v")] == 0:
                    md[i,md_col_list.index("b-v")] = -1000  # indicate from bad measurments - e.g. both values set to -1000
                md[i,md_col_list.index("v-r")] = measured_machine_mags[i,mmm_col_lst.index("v")] - measured_machine_mags[i,mmm_col_lst.index("r")]
                if md[i,md_col_list.index("v-r")] == 0:
                    md[i,md_col_list.index("v-r")] = -1000  # indicate from bad measurments - e.g. both values set to -1000
                md[i,md_col_list.index("r-i")] = measured_machine_mags[i,mmm_col_lst.index("r")] - measured_machine_mags[i,mmm_col_lst.index("i")]
                if md[i,md_col_list.index("r-i")] == 0:
                    md[i,md_col_list.index("r-i")] = -1000  # indicate from bad measurments - e.g. both values set to -1000
                md[i,md_col_list.index("v-i")] = measured_machine_mags[i,mmm_col_lst.index("v")] - measured_machine_mags[i,mmm_col_lst.index("i")]
                if md[i,md_col_list.index("v-i")] == 0:
                    md[i,md_col_list.index("v-i")] = -1000  # indicate from bad measurments - e.g. both values set to -1000
                md[i,md_col_list.index("b-r")] = measured_machine_mags[i,mmm_col_lst.index("b")] - measured_machine_mags[i,mmm_col_lst.index("r")]
                if md[i,md_col_list.index("b-r")] == 0:
                    md[i,md_col_list.index("b-r")] = -1000  # indicate from bad measurments - e.g. both values set to -1000
                md[i,md_col_list.index("b-i")] = measured_machine_mags[i,mmm_col_lst.index("b")] - measured_machine_mags[i,mmm_col_lst.index("i")]
                if md[i,md_col_list.index("b-i")] == 0:
                    md[i,md_col_list.index("b-i")] = -1000  # indicate from bad measurments - e.g. both values set to -1000
                    
                    
                    
                                       
# Create list of instructions to generate transforms - list element sequence is  - transform, x values, y values,(Y/N inverse indicator)
            transform_inst = ["Tub","U-B","u-b","Y","Tbv","B-V","b-v","Y","Tbr","B-R","b-r","Y","Tbi","B-I","b-i","Y","Tvr","V-R","v-r","Y",
                       "Tri","R-I","r-i","Y","Tu_ub","U-B","U-u","N","Tb_ub","U-B","B-b","N",
                       "Tb_bv","B-V","B-b","N","Tb_br","B-R","B-b","N","Tb_bi","B-I","B-b","N","Tv_bv","B-V","V-v","N","Tv_vr","V-R","V-v","N",
                       "Tr_vr","V-R","R-r","N","Tr_ri","R-I","R-r","N",
                       "Ti_ri","R-I","I-i","N","Tvi","V-I","v-i","Y","Tv_vi","V-I","V-v","N","Ti_vi","V-I","I-i","N",
                       "Tr_vi","V-I","R-r","N"]
            
            
                        
                        
# Create master array 'transform_raw_data' indexed by transform name index, star id number, and x values, y values,and indicator if star is use for transform calculation (1=Y,0=N)
#           
# Determine which filters were submitted and create valid transform_names list to be computed given those filters
            transform_names = [] # initialize list of transforms to be computed
            
            if u_ind == 1 and b_ind == 1:
                transform_names.append("Tub")
                transform_names.append("Tu_ub")
                transform_names.append("Tb_ub")
            if b_ind == 1 and v_ind == 1:
                transform_names.append("Tbv")
                transform_names.append("Tb_bv")
                transform_names.append("Tv_bv")
            if v_ind ==1 and r_ind == 1:
                transform_names.append("Tvr")
                transform_names.append("Tv_vr")
                transform_names.append("Tr_vr")
            if r_ind == 1 and i_ind ==1:
                transform_names.append("Tri")
                transform_names.append("Tr_ri")
                transform_names.append("Ti_ri")
            if v_ind ==1 and i_ind ==1:
                transform_names.append("Tvi")
                transform_names.append("Tv_vi")
                transform_names.append("Ti_vi")
                if r_ind == 1:
                    transform_names.append("Tr_vi")
                    
            if b_ind ==1 and r_ind == 1:
                transform_names.append("Tbr")
                transform_names.append("Tb_br")
            if b_ind ==1 and i_ind == 1:
                transform_names.append("Tbi")
                transform_names.append("Tb_bi")
################################################
# add ability to calculate Tv_bv etc. for single filter transforms
            filters_submitted = [b_ind,v_ind,r_ind,i_ind]
            single_filter_transforms = ["Tb_bv","Tv_bv","Tr_vi","Ti_vi"]
            num_submitted = 0
            for counter in range(len(filters_submitted)): # count number of filters with data submitted
                if filters_submitted[counter] == 1:
                    indexnum = counter
                    num_submitted += 1
            if num_submitted == 1: # only one filter data submitted - for single filter transforms
                transform_names.append(single_filter_transforms[indexnum])
################################################
            
            if len(transform_names) == 0 :  # check that some transform values can be calculated
                Errormsg("No standard transforms can be computed with filters submitted")
                return
#
#  Go to method to calculate actual transforms
#
            transform_calc(transform_names,num_meas_stars,transform_inst,md)
#
############################################################
#  Display Transforms on Menu - link to Plot/Refine Window #
############################################################
#
#
#  Title lines
            fl_meas_JD = float(meas_JD)
            tel = tel_id
            lab_text = "    Telescope = " + tel + "\nJulian Date =" + str(meas_JD)
            titlab = []
            tittext = ["    Transform Values",lab_text,"  Select Transforms for\n   Review and Analysis"]
            for i in range(3):
                titlab.append(Text(app,width=24,height=2,bg="#E0FFFF",pady=3,padx=30))
                titlab[i].insert(0.0,tittext[i])
                titlab[i].grid(column=0,columnspan=3,sticky = "W",row=10+i)
            
                
# Display Selectable Transform lines - user can select for more detail plot and revision
            labrow = 14 # top display screen line for tranforms
            labcol = 0  # left column for screen display
            txtboxlab = []  # tuple for names of text boxes
            i = 0
            for line in transform_names:
                txtboxlab.append(Text(app,width=40,height=1,insertontime=0))
                temphold = " =  %6.3f err = %4.3f r^2 = %3.2f" % (transform_val[transform_names.index(line)],
                                                                  transform_val_err[transform_names.index(line)],transform_val_r2[transform_names.index(line)])
                line_text = line.ljust(7) + temphold
                txtboxlab[i].insert(0.0,line_text)
                txtboxlab[i].grid(column=0,row=labrow+i,sticky="W",columnspan=3)
                txtboxlab[i].bind("<1>", lambda event: txtboxlab[i].focus.set())
                txtboxlab[i].bind('<Button-1>',line_pick)
                txtboxlab[i].bind('<Enter>',on_enter)
                txtboxlab[i].bind('<Leave>',on_leave)
                labrow = labrow + 1
                i = i + 1
            save_xform_button.configure(state = "active",activebackground = "#E0FFFF", bg= "#E0FFFF")  # activate save transform button
            
#
# END OF CODE DISPLAYING TRANSFORMATION ON PRIMARY ROOT WINDOW-----------------------------------------------------------------------------------------------------
#
           
            
            

#################################################################################
# Calculate transforms for display on root Transforms Calculation Window        #
#################################################################################
#
def transform_calc(transform_names,num_meas_stars,transform_inst,md):
    """ Create transform_raw_data array containing specific data required for each transform, for example all U-b and U-B measurements for the Tub transform """
    global x,y,transform_data,md_col_list,meas_JD,transform_val,transform_raw_data,fig1,transform_val_err,transform_val_r2,transform_std_error
    transform_raw_data = np.zeros((len(transform_names),num_meas_stars,5))
    for tname in transform_names:
        for m1 in range(num_meas_stars):
            transform_inst_index_x = transform_inst.index(tname) + 1 # location of x column name in transfor_inst_index
            transform_inst_index_y = transform_inst_index_x + 1
            transform_raw_data[transform_names.index(tname),m1,0] = m1  # measurement number internal identifier
            transform_raw_data[transform_names.index(tname),m1,1] = md[m1,md_col_list.index(transform_inst[transform_inst_index_x])] # "x" value
            transform_raw_data[transform_names.index(tname),m1,2] = md[m1,md_col_list.index(transform_inst[transform_inst_index_y])] # "y" value
            if (abs(transform_raw_data[transform_names.index(tname),m1,1]) +  abs(transform_raw_data[transform_names.index(tname),m1,2]) > 200) :
                transform_raw_data[transform_names.index(tname),m1,3]= 2  # Set "in use" indicator to never use - => bad measurement or standard data
            else :
                transform_raw_data[transform_names.index(tname),m1,3]= 1   # Set "in use" to be used (may be changed later by user)
            transform_raw_data[transform_names.index(tname),m1,4] = md[m1,md_col_list.index("Star_id_index")] # save standard star name id number
# Remove data points from bad measurements for least squares fit - ALL TRANSFORMS, first time (prior to user interaction)
    transform_val = []
    transform_val_err = []
    transform_val_r2 = []
    for tname in transform_names:
        xinter = np.zeros(num_meas_stars) # create
        yinter = np.zeros(num_meas_stars) # create
        m5 = 0
        for m4 in range(num_meas_stars):
            if transform_raw_data[transform_names.index(tname),m4,3]== 1:   # good data?
                xinter[m5] = transform_raw_data[transform_names.index(tname),m4,1]
                yinter[m5] = transform_raw_data[transform_names.index(tname),m4,2]
                m5 = m5+1
        x = xinter[0:m5]
        y = yinter[0:m5]
        slope,intercept,r_value,p_value,slope_std_error = stats.linregress(x,y) # Calculate least squares fit
        trform = slope
        transform_std_error = slope_std_error
        if transform_inst[transform_inst.index(tname) +3] == "Y":  # Create reciprocal if needed
            trform = 1/slope
            transform_std_error = slope_std_error/(slope*(slope-slope_std_error))
        transform_val.append(trform)
        transform_val_err.append(transform_std_error)
        transform_val_r2.append(r_value**2)
        
        
        
    
    

########################################################
#         End of transforms displayed in root window   #
########################################################

    

####################################################################################
#                                                                                  #
#   Event handlers for transform list on home page                                 #
#                                                                                  #
####################################################################################
def on_enter(event):
    event.widget.configure(background = "red", foreground = "yellow")
def on_leave(event):
    event.widget.configure(background = "white", foreground = "black")
def line_pick(event):
    global pick_line,tname,selected_star_textlab,ax,fig1,xends_sigma_orig,yends_sigma_orig
    pick_line = event.widget.get(0.0,END)
    temp = pick_line[0:6] # select transform letters from text line selected
    tname = temp.strip()
    plt.ioff() # turn off interactive matplotlib
    try:
        plt.close(fig1) # close any open figure
    except:
        dummy = 0
    selected_star_textlab = "  "  # No message to display on first call
    xends_sigma_orig = np.zeros(2)  # set up to track original 3 sigma lines on plot
    yends_sigma_orig = np.zeros(2)
    figure(figsize=(7,7),dpi=120)
    fig1 = plt.figure(1)  # start figure 1
   
##
##  Add test code to raise window to fron
##
    fig1.canvas.manager.window.attributes('-topmost',1) # place window on top
    fig1.canvas.manager.window.attributes('-topmost',0) # allow later windows on top
    
##
##
    ax = fig1.add_subplot(111) # added subplot so pick works on Mac
    fig1.canvas.mpl_connect('pick_event',onpick) # Set up pick for user to select points
    calculate_plot_transform()        
    plt.show(block=True)  # try no break  - works OK on PC  


                  
        

###############################################################################
#                                                                             #
#  Re-compute transform based on User selection of points in and out of use   #
#  Queued by User selecting point on plot                                     #
#                                                                             #
###############################################################################
def onpick(event):
    global transform_data,transform_raw_data,num_meas_stars,num_good_meas,num_used_meas,use,x,y,first_plot,changed_point
    global transform_inst,tname,transform_label,fig1,selected_star_textlab,change_star_id_msg,old_pick_time,ax,predict_y,x
    global txtboxlab,slope_std_error,r_value,transform_val_err,transform_val_r2,star_id_list,xends,yends,transform_std_error
    thisline = event.artist # event id
    xdata = thisline.get_xdata()
    ydata = thisline.get_ydata()
    ind = event.ind
    for j in range(num_meas_stars): # find point selected
        if transform_raw_data[transform_names.index(tname),j,1] == xdata[ind] and transform_raw_data[transform_names.index(tname),j,2] == ydata[ind]:
            if transform_raw_data[transform_names.index(tname),j,3] == 1: # is measurement currently in use?
                transform_raw_data[transform_names.index(tname),j,3] = 0 # switch to not used
                lab1 = " removed from calculation"
            else:
                transform_raw_data[transform_names.index(tname),j,3] = 1  # switch to used
                lab1 = " added to calculation"
            changed_point = j
            xmin, xmax = plt.xlim()
            ymin, ymax = plt.ylim()
            star_meas_id = int(transform_raw_data[transform_names.index(tname),j,4]) # standard star id name index
            selected_star_textlab =  " Reference Star " + star_id_list[star_meas_id] + lab1
            transform_label.remove() # remove previous transform label
            change_star_id_msg.remove() # remove previous star selected message

# Go to plot routine
    ax.clear() # clear previous plot
 #   predict_plot = ax.plot(xends,yends, 'k-') # replot last line in black temporary removal
    trform = calculate_plot_transform() # go to interactive transform calculation and plot new data creation

# Update root page
    transform_val[transform_names.index(tname)] = trform
    transform_val_err[transform_names.index(tname)] = transform_std_error  # calculated in calculate_plot_transform()
    transform_val_r2[transform_names.index(tname)] = r_value**2
    line_text = tname.ljust(7) +" =  %6.3f" % trform + " err = %4.3f" % transform_std_error + " r^2 = %3.2f" % r_value**2
    row = 14 + transform_names.index(tname)
    txtboxlab[row-14].delete(1.0, END)  # clear previous text
    txtboxlab[row-14].insert(0.0,line_text)
    
# Update plot
    plt.draw() 
  #  plt.show(block=False) # trial on onpick use of show without block instead - help mac events?             
    


    
#######################################################################################################################
#                                                                                                                     #
#   Interactive (on Plot window) Calculation and Display of single transform showing used and unused measurements     #
#   and allowing user to select and deselect measurements used in the calulation.  It is used both on initial         #
#   request for plot from root window, and interactively when user changes use of a measurment                        #
#                                                                                                                     #
#######################################################################################################################
def calculate_plot_transform():
    global transform_data,transform_raw_data,num_meas_stars,num_good_meas,num_used_meas,use,x,y,first_plot,changed_point,ax,predict_y,x,xends,yends
    global transform_inst,x_in_use,y_in_use,tname,transform_label,predict_plot,num_good_meas,fig1,selected_star_textlab,change_star_id_msg,ax,slope_std_error,r_value
    global xends_3sigma_orig,yends_3sigma_orig,orig_sigma,transform_std_error,xends_sigma_orig,yends_sigma_orig,orig_sigma
    xends = np.zeros(2) # id min and max x
    m5 = 0 # counter for selected measurements
    m6 = 0 # counter for valid measurements
    
    xinter = np.zeros(num_meas_stars)  # will hold all measurements selected for use
    yinter = np.zeros(num_meas_stars)  # will hold all measurements selected for us
    xallvalid = np.zeros(num_meas_stars)  # will hold all valid measurements in original downloaded file
    yallvalid = np.zeros(num_meas_stars)  # will hold all valid measurements in original downlaoded file
    
#  print("num_meas_stars=",num_meas_stars)
    for m4 in range(num_meas_stars):  # find valid star to initialize ends
   #     print("m4,transform_raw_data[transform_names.index(tname),m4,3],transform_raw_data[transform_names.index(tname),m4,1]\n",m4,transform_raw_data[transform_names.index(tname),m4,3],transform_raw_data[transform_names.index(tname),m4,1])
        if transform_raw_data[transform_names.index(tname),m4,3] < 2:  # valid star measurement
            xends[0] = transform_raw_data[transform_names.index(tname),m4,1]  # set min to first valid measurement
            xends[1] = transform_raw_data[transform_names.index(tname),m4,1]  # set max to first valid measurement
            break
    for m4 in range(num_meas_stars):  # save stars being used in calculation and all valid stars (separate files)
        if transform_raw_data[transform_names.index(tname),m4,3]== 1:
            xinter[m5] = transform_raw_data[transform_names.index(tname),m4,1]
            yinter[m5] = transform_raw_data[transform_names.index(tname),m4,2]
            m5 = m5+1
        if transform_raw_data[transform_names.index(tname),m4,3] != 2: # find all valid stars for plotting
            xallvalid[m6] = transform_raw_data[transform_names.index(tname),m4,1]
            yallvalid[m6] = transform_raw_data[transform_names.index(tname),m4,2]
            m6 = m6 + 1
            if transform_raw_data[transform_names.index(tname),m4,1] < xends[0]:  # find min for plot range
                xends[0] = transform_raw_data[transform_names.index(tname),m4,1]
            if transform_raw_data[transform_names.index(tname),m4,1] > xends[1]:  # find max for plot range
                xends[1] = transform_raw_data[transform_names.index(tname),m4,1]
#
#  Get fit using all valid stars to create guidelines on plot for 2 sigma original fit
#
    x = xallvalid[0:m6]
    y = yallvalid[0:m6]
    slope,intercept,r_value,p_value,slope_std_error = stats.linregress(x,y) # Calculate least squares fit using all measurementss
    #
#  Calculate Y standard error using all measurements
#
    num_points = len(x)
    y_err_squared_sum = 0
    for i in range(num_points):
        y_err_squared_sum += (y[i] - intercept - slope*x[i])**2
    y_std_error = np.sqrt(y_err_squared_sum/(num_points - 2))
    yends = slope * xends + intercept # compute predicted y values at ends of plot
    xends_sigma_orig = xends
    yends_sigma_orig = yends
    orig_sigma = y_std_error

#
#  Calculaate Fit parameters using only selected points


    x = xinter[0:m5]
    y = yinter[0:m5]
            
    #
    #  calculate least squares
    #
    slope,intercept,r_value,p_value,slope_std_error = stats.linregress(x,y) # Calculate least squares fit
    trform = slope
    transform_std_error = slope_std_error
   # debug line print("slope_std_error ",slope_std_error)
#
#  Calculate Y standard error using all selected points
#
    num_points = len(x)
    y_err_squared_sum = 0
    for i in range(num_points):
        y_err_squared_sum += (y[i] - intercept - slope*x[i])**2
    y_std_error = np.sqrt(y_err_squared_sum/(num_points - 2))
    yends = slope * xends + intercept # compute predicted y values at ends of plot
#####
        
    if transform_inst[transform_inst.index(tname) +3] == "Y":  # Create reciprocal if needed
        trform = 1/slope
        transform_std_error = slope_std_error/(slope*(slope-slope_std_error))

    
    for i in range(num_meas_stars):  # plot one point at a time so color can be switched later
        if transform_raw_data[transform_names.index(tname),i,3] == 1:
            clr = "green"
        elif transform_raw_data[transform_names.index(tname),i,3] == 0:
            clr = "red"
        if transform_raw_data[transform_names.index(tname),i,3] != 2 :
            ax.plot(transform_raw_data[transform_names.index(tname),i,1],transform_raw_data[transform_names.index(tname),i,2],"o",color=clr, picker=5)#       
    

    yends = slope * xends + intercept # compute predicted y values at ends of plot
 #   print("xends_3sigma_orig,yends_3sigma_orig,orig_sigma",xends_3sigma_orig,yends_3sigma_orig,orig_sigma)
# Always show original 3 sigma lines
#    print("xends_3sigma_orig,yends_3sigma_orig,orig_sigma",xends_3sigma_orig,yends_3sigma_orig,orig_sigma)
    ax.plot(xends_sigma_orig,yends_sigma_orig + 2*orig_sigma,"m-",linewidth=2)
    ax.plot(xends_sigma_orig,yends_sigma_orig - 2*orig_sigma,"m-",linewidth=2)
# plot current fit and 3 sigma lines     
    predict_plot = ax.plot(xends,yends, 'r-')
    ax.plot(xends,yends + 2*y_std_error,'b:',linewidth=2)
    ax.plot(xends,yends - 2*y_std_error,'b:',linewidth=2)
    ax.set_xlabel(transform_inst[transform_inst.index(tname)+1])
    ax.set_ylabel(transform_inst[transform_inst.index(tname)+2])
    ax.set_title(tname)
    textlab = tname + " =  %5.3f" % trform + " err = %4.3f" % transform_std_error + "  R^2 = %3.2f" % r_value**2 + "  # ref stars = %3.0f" % m5
    xmin, xmax = plt.xlim()
    ymin, ymax = plt.ylim()
    delx = xmax-xmin
    dely = ymax-ymin    
    transform_label = ax.text(.05*(xmax-xmin)+xmin,.95*(ymax-ymin)+ymin,textlab)
    change_star_id_msg = ax.text(xmin+.01*delx,ymin+.01*dely,selected_star_textlab) # Display new star selected message
    ymsg = .05*dely + ymin
    yline = ymsg - .01*dely
    ax.text(.1*delx+xmin,ymsg,"Current Fit ")
    ax.text(.4*delx+xmin,ymsg,"Current 2 sigma")
    ax.text(.7*delx+xmin,ymsg,"All Measurements 2 sigma")
    ax.plot((.1*delx+xmin,.3*delx+xmin),(yline,yline),'r-')
    ax.plot((.4*delx+xmin,.6*delx+xmin),(yline,yline),'b:',linewidth=2)
    ax.plot((.7*delx+xmin,.9*delx+xmin),(yline,yline),'m-',linewidth=2)
    
# return to either show() or draw()
    return trform





###############################################################################
#                                                                             #
#              General Purpose classes and methods                            #
#                                                                             #
###############################################################################


############################################
#  Display Error Mesage Window Class       #
############################################          
                    
                            
# Create Error Message Class
class Errormsg():
    def __init__(self,message):
        self.errwindow = Toplevel()
        self.errwindow.title("Error Message")
#        self.errwindow.geometry("400x200")
        textmsg = Label(self.errwindow,text=("   "+ message),background = "red",font="12").grid(columnspan=4)
        Button(self.errwindow,text="OK",command = self.quit,font="12").grid(columnspan=4)
    def quit(self):
        self.errwindow.destroy()

##############################################
# Create Message Box                         #
##############################################

class MessageBox():
    def __init__(self,message):
        self.msgwindow = Toplevel()
        self.msgwindow.title("Message")
 #       self.msgwindow.geometry("400x150")
        Label(self.msgwindow,text=("   "+ message),background = "pale green",font="12").grid(columnspan=5)
        Button(self.msgwindow,text="OK",command = self.quit,font="12").grid(columnspan=5)
       
    def quit(self):
        self.msgwindow.destroy()
    

##############################################
# Create single line two radiobutton widget  #
##############################################

class SevenRadioButton():
    def __init__(self,master,linetag,btn1name,btn2name,btn3name,btn4name,btn5name,btn6name,btn7name,line,col,var):
        Label(master,text=linetag,font=12,bg="#E0FFFF").grid(row=line,column=col,columnspan=1,sticky="E")
        Radiobutton(master,text=btn1name,variable=var,value=btn1name,font=12).grid(row=line,column=col+1,sticky = "w", pady=5)
        Radiobutton(master,text=btn2name,variable=var,value=btn2name,font=12).grid(row=line,column=col+2,sticky = "w", pady=5)
        Radiobutton(master,text=btn3name,variable=var,value=btn3name,font=12).grid(row=line,column=col+3,sticky = "w", pady=5)
        Radiobutton(master,text=btn4name,variable=var,value=btn4name,font=12).grid(row=line,column=col+4,sticky = "w", pady=5)
        Radiobutton(master,text=btn5name,variable=var,value=btn5name,font=12).grid(row=line,column=col+5,sticky = "w", pady=0)
        Radiobutton(master,text=btn6name,variable=var,value=btn6name,font=12).grid(row=line,column=col+6,sticky = "w", pady=5)
        Radiobutton(master,text=btn7name,variable=var,value=btn7name,font=12).grid(row=line,column=col+7,sticky = "w", pady=5)
##############################################
# Parse line into list                       #
##############################################

def lineparse(line,linelist,delim):
    i=0
    for j in range (i,len(line)):
        if line[j] == delim[0] or line[j] == delim[1]:  # Allow two delimiters
            temp = line[i:j].strip()
            linelist.append(temp)
            i=j+1
    if i<j and i != len(line): # check field to right of last delimiter for content 
        temp = line[i:].strip()
        if temp != "":
            linelist.append(temp)

#############################################
# Create Get File Name button method        #
#############################################

def get_file_name():
    global magfilenam,tel_id,caltransformsbutton,titlab,filelabel,file_namelist
    if tel_id == "Add Scope":
        Errormsg("Select Telescope Name first")
    else:
        fn = askopenfilenames() # may be multiple files if VPHOT
        file_namelist = root.tk.splitlist(fn)
        filelabel.delete(1.0,END)  # clear previous text
        filelabel.insert(0.0,fn)
        magfilenam = file_namelist[0]
# erase any previous transform calculations from menu
        try:
            for i in range(len(transform_names)) :
                txtboxlab[i].destroy()
            for i in range(4) :
                titlab[i].destroy()
        except:
            dummy = 0  # no previous transforms calculated
        caltransformsbutton.configure(state = "active",activebackground = "#E0FFFF",bg="#E0FFFF")

#############################################
#   Telescope id ComboBox pick method       #
#############################################
def tel_id_pick(event):
    global tel_id_win,tel_id,tel_id_entry,merge_obs_sets_button,tel_id_box,tel_id_list
    merge_obs_sets_button.configure(activebackground = "#E0FFFF",state = "active",bg="#E0FFFF")
    getfilnamebutton.configure(state = "active",activebackground = "#E0FFFF",bg="#E0FFFF")
    delete_obs_sets_button.configure(state = "active",activebackground = "#E0FFFF",bg="#E0FFFF")
    tel_id = tel_id_box.get()
    if tel_id == "Add Scope":
        tel_id_win = Toplevel()
        tel_id_win.title("Add Telescope")
        tel_id_win.geometry(("300x100"))
        tel_id_entry = Entry(tel_id_win)
        tel_id_entry.grid(sticky = W,row=1)
        enter_button = Button(tel_id_win,text="Enter", command = save_new_tel_id)
        enter_button.grid(row=3)
        


def save_new_tel_id():
    global tel_id_list,tel_id,tel_id_entry,tel_id_win,tel_id_box
    tel_id = tel_id_entry.get()
    tel_id = tel_id.strip()
# Check if scope already in list
    for i in range(1,len(tel_id_list)):
        if tel_id == tel_id_list[i]:
            Errormsg("Telescope " + tel_id + " already in list")
            return
        
    if len(tel_id) > 0:   # Be sure something is entered     
        config_file = open("Photometry_Transform_Config_Data.txt","a") # new entry - add to file - open with append option
        linetext = "Telescope_id;" + tel_id + ";\n"  #add scope to permanent telescope list
        config_file.write(linetext)
        config_file.close()
        tel_id_list.append(tel_id)
        Label(app,text= "   Telescope Name " + tel_id + " added to list",bg="#7CFC00").grid(row=0,column=2,columnspan=2)
        tel_id_box.configure(values=tel_id_list)
        tel_id_box.current(tel_id_list.index(tel_id))
        tel_id_box.grid(column=1,row=0)
    else:
        Errormsg("Telesope id can not be blank")
    tel_id_win.destroy()
    

    
######################################################
#        Save Transforms                             #
######################################################

def savetransforms():
    global transform_names,transform_val,transform_val_err,transform_val_r2,meas_JD,tel_id,std_field_name
    curtime = strftime("%Y%m%d%H%M%S",gmtime())
    record = [tel_id,meas_JD,curtime,transform_names,transform_val,transform_val_err,transform_val_r2,std_field_name]
    transform_file = open("transform_values.ptgp","ab")
    pickle.dump(record,transform_file)
    transform_file.close()
    msgtxt = curtime[0:4] + "-" + curtime[4:6] + "-" + curtime[6:8] + "  " + curtime[8:10] +":" + curtime[10:12] + ":" + curtime[12:]
    MessageBox("Transforms saved at UT\n " + msgtxt)

###############################################################################
###############################################################################
##                                                                           ##
##         Create New Menu to Allow deletion of Transform Sets               ##
##   Triggered by "Delete Old Transform Seets" button on main window         ##
##                                                                           ##
###############################################################################
###############################################################################

def deletesets():
    global tel_id,tel_id_saved_xforms,record,obspicklist,root2,deletewindow
# Create new window
    deletewindow = Toplevel()
    deletewindow.title("Delete Transform Sets - " + version)
    deletewindow.geometry(("1200x800"))
    root3 = Frame(deletewindow)
    root3.grid()
    Label(root3,text=("Telescope " + tel_id),font=12).grid(row=0,columnspan=8)
    Label(root3,text=("---------" * 8)).grid(row=1,column=0,columnspan=8)
    Label(root3,text="Select Transform Sets for Deletion",font="10").grid(row=2,column=0,columnspan=2)
    Label(root3,text="(Up to 6)",font="10").grid(row=3,column=0,columnspan=2)
    Label(root3,text="(Obs JD -- transform save date -- std field)").grid(row=4, column=0,columnspan=2)
    Label(root3,text="(JD--YY_MM_DD_HH:MM:SS -- field name)").grid(row=5,column=0,columnspan=2)    
    tel_id_saved_xforms = []
    transform_file = open("transform_values.ptgp","rb")
    count = 0  # set count of number of records for telescope
    for i in range(1000):  # get all records for selected telescope
        try:
            record = pickle.load(transform_file)
            if record[0] == tel_id:
                tel_id_saved_xforms.append(record)
                count = count + 1
        except:
            break # end of file
            
    listobs = "" # create string of obs set julian date + transform create date/time
# Set up scrolled listbox
    myframe = Frame(root3)
#    myframe.pack(side=RIGHT, fill=Y) - remove causing mac problem
    scrollbar = Scrollbar(myframe)
    scrollbar.pack(side=RIGHT,fill=Y)
    obspicklist = Listbox(myframe,height = 15, selectmode="multiple",width=40,bg = "white",yscrollcommand=scrollbar.set)
    obspicklist.pack()
    scrollbar.config(command=obspicklist.yview)
    myframe.grid(row = 6, columnspan = 2, rowspan=12,)
    for i in range(count):  # for each record from scope list obs and transform calculation times
        record = tel_id_saved_xforms[i]
        try:
            modified_JD = str(float(record[1]) - 2450000.)
        except:
            record[1] = 2460000  # if invalid JD, set to 2460000
            modified_JD = "10000"
        modified_JD = modified_JD[:8]
        st = record[2]
        savetimeformatted = st[2:4]+"_"+st[4:6]+"_"+st[6:8]+ "_" +st[8:10] +":"+st[10:12]+":"+st[12:]
        jul_date_meas_save = " " + str(modified_JD) + " -- " + savetimeformatted + " -- " + record[7]  # record[7] = standard field name
        obspicklist.insert(END,jul_date_meas_save)    
    get_obs_to_use_list = Button(root3,text = "Delete transform sets",command = deletelist,font=10,bg="#E0FFFF").grid(row=20,columnspan=2)

###########################################################################################
#  Process Delete transform list button
###########################################################################################
def deletelist():
    global obspicklist,allxforms, tel_id_saved_xforms,root2,obs_set_checkbox,remove_col,obs_selected,max_selected_sets,hold_transform_values_in_memory,deletewindow
    obs_selected = obspicklist.curselection()
#    print("obs_selected ", obs_selected)
    transform_file_current = open("transform_values.ptgp","rb")
    hold_ptgp_record_in_memory = []
    for i in range(10000):  # get all records
        try:
            record_line = pickle.load(transform_file_current)
            hold_ptgp_record_in_memory.append(record_line)
        except:
            break # end of file
    transform_file_current.close()
    transform_file_current = open("transform_values.ptgp","wb")  # open allowing overwrite of current file
    j = -1 # start count of tel_id records 
    for i in range(len(hold_ptgp_record_in_memory)):
        if hold_ptgp_record_in_memory[i][0] != tel_id: # was this record on displayed list?
            pickle.dump(hold_ptgp_record_in_memory[i],transform_file_current) # no, so write out line
            continue
        j += 1  # increment count of tel_id records found
        if j in obs_selected:
            continue # match - don't write out
        if str(j) in obs_selected:  # allow for Mac where obs_selected are string variables
            continue # Mac match - don't write out
#        print("Got to pickle - j=",j)
        pickle.dump(hold_ptgp_record_in_memory[i],transform_file_current) # write out line
    transform_file_current.close()
    MessageBox("  Transform Sets Successfully Removed  ")
    deletewindow.destroy()
    
###############################################################################
###############################################################################
##                                                                           ##
##           Create New Menu to Enable Transform Sets to be averaged         ##
##   Triggered by "Select/Average Transform Sets" button on main window      ##
##                                                                           ##
###############################################################################
###############################################################################
#
def myfunction2(event):
    global canvas2
    canvas2.configure(scrollregion=canvas2.bbox("all"))
#
def mergesets():
    global tel_id,tel_id_saved_xforms,record,obspicklist,root2,canvas2
# Create new window
    mergewindow = Toplevel()
    mergewindow.title("Review and Average Different Transform Sets - TG " + version)
    mergewindow.geometry("800x600")
    canvas2 = Canvas(mergewindow)
    root2 = Frame(canvas2)
    root2.bind("<Configure>",myfunction2)
    canvas2.create_window((0,0),window=root2,anchor="nw")
    mergewindowscrollbary = Scrollbar(canvas2,orient="vertical",command=canvas2.yview)
    canvas2.configure(yscrollcommand=mergewindowscrollbary.set)
    mergewindowscrollbary.pack(side=RIGHT,fill=Y)
    mergewindowscrollbarx = Scrollbar(canvas2,orient="horizontal",command=canvas2.xview)
    canvas2.configure(xscrollcommand=mergewindowscrollbarx.set)
    mergewindowscrollbarx.pack(side=BOTTOM,fill=X)
    canvas2.pack(side=TOP,fill=BOTH,expand=TRUE)
    Label(root2,text=("Telescope " + tel_id),font=12).grid(row=0,columnspan=8)
    Label(root2,text=("---------" * 8)).grid(row=1,column=0,columnspan=8)
    Label(root2,text="Select Transform Sets",font="10").grid(row=2,column=0,columnspan=2)
    Label(root2,text="(Up to 6)",font="10").grid(row=3,column=0,columnspan=2)
    Label(root2,text="(Obs JD -- transform save date -- std field)").grid(row=4, column=0,columnspan=2)
    Label(root2,text="(JD--YY_MM_DD_HH:MM:SS -- field name)").grid(row=5,column=0,columnspan=2)    
    tel_id_saved_xforms = []
    transform_file = open("transform_values.ptgp","rb")
    count = 0  # set count of number of records for telescope
    for i in range(1000):  # get all records for selected telescope
        try:
            record = pickle.load(transform_file)
            if record[0] == tel_id:
                tel_id_saved_xforms.append(record)
                count = count + 1
        except:
            break # end of file
            
    listobs = "" # create string of obs set julian date + transform create date/time
# Set up scrolled listbox
    myframe = Frame(root2)
    scrollbarlistbox = Scrollbar(myframe)
    scrollbarlistbox.pack(side=RIGHT,fill=Y)
    obspicklist = Listbox(myframe,height = 15, selectmode="multiple",width=40,bg = "white",yscrollcommand=scrollbarlistbox.set)
    obspicklist.pack()
    scrollbarlistbox.config(command=obspicklist.yview)
    myframe.grid(row=6, columnspan = 2, rowspan=12)
    for i in range(count):  # for each record from scope list obs and transform calculation times
        record = tel_id_saved_xforms[i]
        try:
            modified_JD = str(float(record[1]) - 2450000.)
        except:
            record[1] = 2460000  # if invalid JD, set to 2460000
            modified_JD = "10000"
        modified_JD = modified_JD[:8]
        st = record[2]
        savetimeformatted = st[2:4]+"_"+st[4:6]+"_"+st[6:8]+ "_" +st[8:10] +":"+st[10:12]+":"+st[12:]
        jul_date_meas_save = " " + str(modified_JD) + " -- " + savetimeformatted + " -- " + record[7]  # record[7] = standard field name
        obspicklist.insert(END,jul_date_meas_save)    
    get_obs_to_use_list = Button(root2,text = "Retrieve transform sets",command = getlist,font=10,bg="#E0FFFF").grid(row=20,columnspan=2)

            
# Method queued when user has selected the sets of observations to review


def getlist():
    global obspicklist,allxforms, tel_id_saved_xforms,root2,obs_set_checkbox,remove_col,obs_selected,max_selected_sets
    max_selected_sets = 6
    try:
        prev_obs_selected = obs_selected # save previous list of obs selected - if any
    except:
        prev_obs_selected = [0]  #  in first time, set to one item to prevent future overwrite of display columns
   
    if len(obspicklist.curselection()) < max_selected_sets + 1:
        obs_selected = obspicklist.curselection()
        obs_set_checkbox = []
        for i in range(len(tel_id_saved_xforms)):  # create list to track which observation sets are checked for use in averaging
            obs_set_checkbox.append("N")  # initialize indicating no checkbox selected
# Display selected observation transform sets for review and remove extra columns
        Label(root2,text="Select Sets to average",font="10").grid(row=2,column=2,columnspan=2,sticky="E")
        Label(root2,text="Julian Date of obs (245xxxx.xxx) ",font="10").grid(row=3,column=2,columnspan=2,sticky="E")
        Label(root2,text="   YY_MM_DD transforms computed",font="10").grid(row=4,column=2,columnspan=2,sticky="E")
        Label(root2,text="HH:MM:SS transforms computed",font="10").grid(row=5,column=2,columnspan=2,sticky="E")
        Label(root2,text="Standards Field (LF=Landolt RA/Dec)",font="10").grid(row=6,column=2,columnspan=2,sticky="E")
        table_start_row=1
        for i in range(len(allxforms)):  # display list of all possible transforms
            Label(root2,text=(allxforms[i] + " "),font="9").grid(row=table_start_row+6+i,column=3,sticky="E")
        remove_col = "N"  # indicate not removing columns
        for i in  range(len(obs_selected)):
            Obs_Set_Columns(root2,(table_start_row+1),(i+4),obs_selected[i]) # Display each column of data
        if len(prev_obs_selected) > len(obs_selected):  # check if previously more columns displayed, if so, remove
            remove_col = "Y"
            for i in range(len(obs_selected),len(prev_obs_selected)):
                dummy = 0  # only so remove process will work - not actually used
                Obs_Set_Columns(root2,(table_start_row+1),(i+4),dummy)
        avg_selected_observations = Button(root2,text = "Compute Average of Checked Transform Sets",command = avg_sets,font=10,bg="#E0FFFF").grid(row=27,column=4,columnspan=10)
        Label(root2, text = " ").grid(row=29,column=4)
    else:
        message = "Reduce to %3.0f or less selections" % max_selected_sets
        Errormsg(message)
##################################################################################        
##################################################################################
#                                                                               ##
#    Create Window to Accept Manual Entry of RA/Dec for standard field center   ##
#                                                                               ##
##################################################################################
##################################################################################
        
def ra_dec_entry_window():
    global raentry,decentry,radecwindow
    radecwindow = Toplevel()
    radecwindow.title("Landolt Field RA/Dec Entry")
    Label(radecwindow, text = "Enter Standard Field Coordinates",font = 12).grid(row=0,column=0,columnspan=2)
    raLabel = Label(radecwindow,text=("RA (HH:MM:SS or DDD.xxx)"),font = 12).grid(row=1,column=0)
    raentry = Entry(radecwindow,font=12)
    raentry.grid(row=1,column=1)
    decLabel = Label(radecwindow,text=("Dec (+/-DD:MM:SS or DD.xxx)"),font=12).grid(row=2,column=0)
    decentry = Entry(radecwindow,font=12)
    decentry.grid(row=2,column=1)
    Button(radecwindow,text="Enter",command = quitra,font="12").grid(row=3,columnspan=2)

def quitra():
    global raentry,decentry,radecwindow,enteredfield
    rainput = raentry.get()
    decinput = decentry.get()
    try:
        if rainput.find(":") > 0 : # if colon found assume HH:MM:SS format
            aline = [] # create holding list for parsed oneline
            delim = [":",":"]  # colon delimeter
            lineparse(rainput,aline,delim)
            searchra = str(15*(float(aline[0])+float(aline[1])/60+float(aline[2])/3600))[:7]
        else:  # assume DDD.xxx format
            searchra = rainput
            
    except:
        Errormsg("Invalid RA Format")
        return
    try:
        if decinput.find(":") > 0 : # if colon found assume +/-DD:MM:SS format
            aline = [] # create holding list for parsed oneline
            delim = [":",":"]  # colon delimeter
            lineparse(decinput,aline,delim)
            searchdec = str(np.sign(float(aline[0]))*(abs(float(aline[0]))+float(aline[1])/60+float(aline[2])/3600))[:7]
        else: # assume DDD.xxx format
            searchdec = decinput
    except:
        Errormsg("Invalid Dec Format")
        return
    enteredfield = "ra="+searchra+"&dec="+searchdec
    radecwindow.destroy()
    
    

    
###########################################################
#                                                         #
#   Class to Display Transform Observation Sets           #
#   as columns on the Merge Obs Sets Window               #
#                                                         #
###########################################################


class Obs_Set_Columns(Frame):
    """ Display Column of Transforms from observation """
    global tel_id_saved_xforms,allxforms,obs_set_checkbox,remove_col,std_field_name
    def __init__(self,master,boxrow,boxcol,obs_id):
        Frame.__init__(self)
#        self.grid()
        self.obs_col_widget(master,boxrow,boxcol,obs_id)
    def obs_col_widget(self,master,boxrow,boxcol,obs_id):  #  Create Display Column with che
        self.use_obs = BooleanVar()
        self.tracking_obs_id = obs_id # save internal obs_id for button checking "update_status"
        self.btn = Checkbutton(master,command=self.update_status,variable = self.use_obs)
        self.btn.grid(row=boxrow,column=boxcol,padx = 2)
        if remove_col == "Y":
            self.btn.configure(state = "disabled")
        self.record = tel_id_saved_xforms[int(obs_id)]
        self.jdtemp = float(self.record[1])-2450000.
        self.jdlinetext = "% 7.3f" % self.jdtemp
        if remove_col == "Y":
            self.jdlinetext = "    "
        self.t1 = Text(master,width=9,height=1,bg="white")
        self.t1.grid(row=boxrow+1,column=boxcol) #obs JD
        self.t1.insert(0.0,self.jdlinetext)
        self.obstime = self.record[2]  # time transform calculated
        self.t2 = Text(master,width=9,height=1)
        self.t2.grid(row=boxrow+2,column=boxcol) # obs YYYYMMDD
        self.obstimefmt = self.obstime[2:4]+ "_" + self.obstime[4:6] + "_" + self.obstime[6:8]
        if remove_col == "Y":
            self.obstimefmt = "  "
        self.t2.insert(0.0,self.obstimefmt)
        self.obshhmmss = self.obstime[8:10] + ":" + self.obstime[10:12] + ":" + self.obstime[12:]
        self.t3 = Text(master,width=9,height=1)
        self.t3.grid(row=boxrow+3,column=boxcol,pady=5) #obs hh:mm
        if remove_col == "Y":
            self.obshhmmss = "  "
        self.t3.insert(0.2,self.obshhmmss)
#  Add code to display standard field used in obervation set
        self.t4 = Text(master,width=10,height=1)
        self.t4.grid(row=boxrow+4,column=boxcol,pady=3) #
        self.field = self.record[7]
        if remove_col == "Y":
            self.field = " "
        self.t4.insert(0.0,self.field)
        self.xforms_calc = self.record[4] #  retrieve computed transforms for observation
        self.xforms_calc_err = self.record[5] # retrieve error values
        self.xforms_calc_r2 = self.record[6] # retrieve r^2 values
        self.xforms_calc_names = self.record[3]
        for i in range(len(allxforms)):
            self.xform_val_txt = "   N/A  "  # default no value if not match found
            for j in range(len(self.xforms_calc_names)):
                if allxforms[i] == self.xforms_calc_names[j]:  # matching transform
                    self.xform_val_txt = "%   7.3f" % self.xforms_calc[j] + "+/-%4.3f" % self.xforms_calc_err[j]
                    break
            self.t4 = Text(master,width=15,height=1, pady = 4)
            if remove_col == "Y":
                self.xform_val_txt = "  N/A "
            self.t4.insert(0.1,self.xform_val_txt)
            self.t4.grid(row= boxrow + 5 + i, column = boxcol)
            
#  method to track check boxes above each columns
    def update_status(self):  #  Track observations picked for use
        if obs_set_checkbox[int(self.tracking_obs_id)] == "Y":
            obs_set_checkbox[int(self.tracking_obs_id)] = "N"
        else:
            obs_set_checkbox[int(self.tracking_obs_id)] = "Y"

##########################################################
#                                                        #
# Routine to average selected transform sets and         #
#                display on screen                       #
##########################################################

def avg_sets():
    global obs_set_checkbox,tel_id_saved_xforms,allxforms,xforms_txt,max_selected_sets,output_file_xform_val_list,output_file_xform_err_list,output_file_xform_r2_list
# Retrieve all transform sets selected
    all_selected_xforms = np.zeros((len(allxforms),max_selected_sets + 1,3)) # first index - transform name index, second index obs set id, third index 0=transform value, 1= err value, 2 = r squared value
# all_selected_xforms final values in cell with second index = max_selected_sets + 1
    for i in range(len(allxforms)):
        for j in range(max_selected_sets + 1):
            for k in range(3):
                all_selected_xforms[i,j,k] = 999  # initialize values to indicate no data
    sel_obs_count = 0  # initialize count of observations selected
    for i in range(len(tel_id_saved_xforms)): # look at every observation record for scope
        if obs_set_checkbox[i] == "Y":   # see if observation to be used
            record = tel_id_saved_xforms[i]  # if yes, get observation set data
            measured_xform_names = record[3]
            measured_xform_values = record[4]
            measured_xform_val_err = record[5]
            measured_xform_val_r2 = record[6]
# debug line           print("meas xform names, values, err, r2 ",measured_xform_names,measured_xform_values,measured_xform_val_err,measured_xform_val_r2)
            for xform in measured_xform_names: # save transform values, errrors, r squared for all selected observation sets
                j = allxforms.index(xform) # just to shorten subsequent typing
                k = measured_xform_names.index(xform)
                all_selected_xforms[j,sel_obs_count,0] = measured_xform_values[k]  # transform value
                all_selected_xforms[j,sel_obs_count,1] = measured_xform_val_err[k]  # transform one sigma error
                all_selected_xforms[j,sel_obs_count,2] = measured_xform_val_r2[k]  # transform r squared
            sel_obs_count += 1
# Calculate mean, error (sigma), and r squared for each transform
#
    if sel_obs_count == 0:  # Be sure at least on transform set selected
        Errormsg("At least one set of transforms must be selected")
        return
    for i in range(len(allxforms)):
        temp_array_val = []
        temp_array_val_err = []
        temp_array_val_r2 = []
        for j in range(max_selected_sets):
            if all_selected_xforms[i,j,0] != 999: # check if transform values present
                temp_array_val.append(all_selected_xforms[i,j,0])  # add value to value list
                temp_array_val_err.append(all_selected_xforms[i,j,1]) # add error to error list
                temp_array_val_r2.append(all_selected_xforms[i,j,2])  # add r squared to r squared list
        if len(temp_array_val) != 0:  # confirm data for given transform available
            all_selected_xforms[i,max_selected_sets, 0] = np.mean(temp_array_val) # compute average value of transform
            temp_err_sq_sum = 0.0 # start error calculation
            for j in range(len(temp_array_val)):
                temp_err_sq_sum = temp_err_sq_sum + temp_array_val_err[j]**2 # add errors squared of initial transform estimates
            all_selected_xforms[i,max_selected_sets, 1] = np.sqrt(temp_err_sq_sum/len(temp_array_val) + np.std(temp_array_val)**2 )# compute RMS of transform error values
            all_selected_xforms[i,max_selected_sets, 2] = np.mean(temp_array_val_r2) # compute average of r squared
# Compute RMS error of combined measurements
        
        
# debug
#    for j in range(len(allxforms)):
#        print("\n next filter, all_selected_xforms[j]",all_selected_xforms[j])

# end debug

#  Display Results and save transform values for potential export
    xforms_txt = [] # text string for display
    output_file_xform_val_list = [] # start list to save lines of transform values
    output_file_xform_err_list = [] # start list to save lines of tranform value errors
    output_file_xform_r2_list = [] # start list to save lines of transform r squared values
    for i in range(len(allxforms)):
        xform_val_txt = "   N/A   "  # default for not data
        if all_selected_xforms[i,max_selected_sets, 0] != 999:
            xform_val_txt = "%   7.3f err= %4.3f r^2= %3.2f"  % (all_selected_xforms[i,max_selected_sets, 0],all_selected_xforms[i,max_selected_sets, 1],all_selected_xforms[i,max_selected_sets, 2])
            
# output file data save
            line = allxforms[i] + "= %5.3f" %  all_selected_xforms[i,max_selected_sets, 0] # transform value line
            output_file_xform_val_list.append(line)
            line = allxforms[i] + "= %5.3f" %  all_selected_xforms[i,max_selected_sets, 1] # transform value error line
            output_file_xform_err_list.append(line)
            line = allxforms[i] + "= %5.3f" %  all_selected_xforms[i,max_selected_sets, 2] # transform value r squared line
            output_file_xform_r2_list.append(line)
            
        xforms_txt.append(xform_val_txt)
        t4 = Text(root2,width=28,height=1,pady=4, bg = "yellow")
        t4.insert(0.1,xform_val_txt)
        t4.grid(row=7+i,column=12)
    Label(root2,text="Avg Transform",bg="yellow").grid(row=3,column=12)

# Add Button to allow saving of average transforms
    save_xforms_btn = Button(root2,text = "Save File of Average Transforms\nEnter/Select File Name\n",command = export_transforms,font=10,bg="#E0FFFF").grid(row=28,column=4,columnspan=10)
    Label(root2, text = " -----------------------\n").grid(row=30)
################################################################################
#                                                                              #
#    Create Export File of Averaged Transforms                                 #
#                                                                              #
################################################################################

def export_transforms():
    global xforms_txt,allxforms,tel_id,output_file_xform_val_list,output_file_xform_err_list,output_file_xform_r2_list
    export_file = asksaveasfile(mode="w",defaultextension = ".ini",parent = root2,
                                title = "Enter Name of Export File")
    curtime = strftime("%Y_%m_%d_%H:%M:%S",gmtime())
    avg_xforms_record = "[Setup]\ndescription= TG" + version 
    avg_xforms_record = avg_xforms_record + ", Telescope= " + tel_id +", Time created (UT) = "+ curtime + "\n[Coefficients]\n"
    for i in range(len(output_file_xform_val_list)):
        avg_xforms_record = avg_xforms_record + output_file_xform_val_list[i] + "\n"
    avg_xforms_record = avg_xforms_record + "[Error]\n"
    for i in range(len(output_file_xform_err_list)):
        avg_xforms_record = avg_xforms_record + output_file_xform_err_list[i] + "\n"
    avg_xforms_record = avg_xforms_record + "[R Squared Values]\n"
    for i in range(len(output_file_xform_r2_list)):
        avg_xforms_record = avg_xforms_record + output_file_xform_r2_list[i] + "\n"
    export_file.write(avg_xforms_record)
    export_file.close()
    fname = export_file.name
    MessageBox("Average Transforms for Telescope " + tel_id + "\nSaved at UT\n" + curtime + " to file\n" + fname)
    
def myfunction(event):
    canvas1.configure(scrollregion=canvas1.bbox("all"))




###################################################################################
###################################################################################
##                                                                               ##
##                    Main Program                                               ##
##                                                                               ##
###################################################################################
###################################################################################
version = " - Version 6.9a"
root = Tk()
root.title("Transformation Generator " + version)
root.geometry("1200x600")
# root.state("zoomed") does not work on Mac
canvas1 = Canvas(root)
app = Frame(canvas1)
app.bind("<Configure>",myfunction)
canvas1.create_window((0,0),window=app,anchor="nw")
appscrollbary = Scrollbar(canvas1,orient="vertical",command=canvas1.yview)
canvas1.configure(yscrollcommand=appscrollbary.set)
appscrollbary.pack(side=RIGHT,fill=Y)
appscrollbarx = Scrollbar(canvas1,orient="horizontal",command=canvas1.xview)
canvas1.configure(xscrollcommand=appscrollbarx.set)
appscrollbarx.pack(side=BOTTOM,fill=X)
canvas1.pack(side=TOP,fill=BOTH,expand=TRUE)
allxforms = ["Tub","Tu_ub","Tb_ub","Tbv","Tb_bv","Tbr","Tb_br","Tb_bi","Tbi","Tv_bv","Tvr","Tv_vr","Tr_vr","Tri","Tr_ri","Ti_ri","Tvi","Tv_vi","Ti_vi","Tr_vi"] # set up master xform list
# Set up master close window handler  WINDOWS UNIQUE CODE

def callback():
    plt.close(1)
    root.destroy()
root.protocol("WM_DELETE_WINDOW", callback)
#
# Define general constants
#
# Define original Henden reference field star ids and map to AUID's  (original id, AUID, RA,DEC)  RA,DEC kept for reference
# NGC7790 reference
ngc7790_AUID_map = []
ngc7790_orig_id_AUID_map = [1,"000-BLJ-963",359.566634,61.280182,
                            2,"000-BLJ-993",359.681309,61.247799,
                            3,"000-BLJ-978",359.674397,61.246143,
                            4,"000-BLJ-991",359.519403,61.271313,
                            5,"000-BLK-002",359.532755,61.245362,
                            6,"000-BLK-000",359.594323,61.236925,
                            7,"000-BLJ-972",359.533764,61.210837,
                            8,"000-000-000",359.530909,61.195801,
                            9,"000-BLJ-981",359.537869,61.190471,
                            10,"000-BLJ-976",359.554895,61.190279,
                            11,"000-000-000",359.572731,61.193578,
                            12,"000-000-000",359.557342,61.176649,
                            13,"000-BLJ-985",359.645726,61.205306,
                            14,"000-BLJ-992",359.645465,61.200245,
                            15,"000-BLJ-989",359.628441,61.131751,
                            16,"000-BLJ-964",359.756764,61.133029,
                            17,"000-BLJ-980",359.723655,61.183857,
                            18,"000-000-000",359.703152,61.209622,
                            19,"000-BLJ-982",359.626446,61.227935,
                            20,"000-BLJ-970",359.596678,61.206957,
                            21,"000-BLJ-987",359.740037,61.162632,
                            22,"000-BLK-004",359.709493,61.167122,
                            23,"000-BLJ-990",359.657828,61.26093,
                            24,"000-BLJ-973",359.71411,61.287535,
                            25,"000-BLK-003",359.793534,61.270575,
                            26,"000-BLK-022",359.571192,61.161605,
                            27,"000-000-000",359.512978,61.137231,
                            28,"000-BLJ-971",359.473495,61.170573,
                            29,"000-BLJ-965",359.508551,61.191277,
                            30,"000-000-000",359.808449,61.154727,
                            31,"000-BLJ-966",359.812589,61.166475]
for i in range(0,31*4,4):
    ngc7790_AUID_map.append([str(ngc7790_orig_id_AUID_map[i]).strip(),ngc7790_orig_id_AUID_map[i+1]]) # original Henden reference numbers and matching AUID
    

#  M67 reference

m67_AUID_map = []
m67_orig_id_AUID_map = [1,"000-000-000",132.799179,11.756206,
                        2,"000-BLG-886",132.821344,11.804549,
                        3,"000-BLG-887",132.845119,11.800557,
                        4,"000-BLG-888",132.861935,11.811315,
                        5,"000-BLG-889",132.802987,11.878504,
                        6,"000-BLG-890",132.870902,11.842597,
                        7,"000-BLG-891",132.93157,11.740761,
                        8,"000-000-000",132.809956,11.750341,
                        9,"000-000-000",132.893091,11.852981,
                        10,"000-BLG-892",132.862659,11.864667,
                        11,"000-BLG-893",132.88592,11.81454,
                        12,"000-BLG-894",132.821106,11.846304,
                        13,"000-BLG-895",132.860242,11.730831,
                        14,"000-BLG-896",132.926626,11.856478,
                        15,"000-BLG-897",132.840744,11.877244,
                        16,"000-BLG-898",132.764746,11.750831,
                        17,"000-BLG-899",132.839951,11.768455,
                        18,"000-000-000",132.849166,11.830434,
                        19,"000-BLG-900",132.937934,11.796177,
                        20,"000-BLG-901",132.782656,11.802645,
                        21,"000-BLG-902",132.926532,11.835538,
                        22,"000-000-000",132.877082,11.81602,
                        23,"000-BLG-903",132.833043,11.783526,
                        24,"000-BLG-904",132.914222,11.862751,
                        25,"000-BLG-905",132.806796,11.843961,
                        26,"000-000-000",132.885851,11.844686,
                        27,"000-BLG-906",132.913576,11.834474,
                        28,"000-BLG-907",132.838534,11.764721,
                        29,"000-BLG-908",132.785038,11.786758,
                        30,"000-BLG-909",132.819685,11.758237,
                        31,"000-BLG-910",132.927937,11.776905,
                        32,"000-000-000",132.829347,11.834994,
                        33,"000-BLG-911",132.855825,11.792925,
                        34,"000-BLG-912",132.926998,11.831179,
                        35,"000-000-000",132.827969,11.784151,
                        36,"000-BLG-913",132.905977,11.834878,
                        37,"000-BLG-914",132.880267,11.764142,
                        38,"000-BLG-915",132.885303,11.797958,
                        39,"000-BLG-916",132.884072,11.834416,
                        40,"000-BLG-917",132.827365,11.822705,
                        42,"000-BLG-918",132.763671,11.76322,
                        41,"000-BLG-919",132.756562,11.826251,
                        43,"000-BLG-920",132.814463,11.792138,
                        44,"000-BLG-921",132.870125,11.866722,
                        45,"000-000-000",132.900157,11.776074,
                        46,"000-000-000",132.845584,11.813799,
                        47,"000-BLG-923",132.877514,11.820411,
                        48,"000-BLG-924",132.924889,11.727077,
                        49,"000-000-000",132.825073,11.765126,
                        50,"000-BLG-925",132.754518,11.836415,
                        51,"000-BLG-926",132.885121,11.80041,
                        52,"000-000-000",132.833954,11.778332,
                        53,"000-BLG-927",132.93348,11.773556,
                        54,"000-BLG-928",132.814043,11.83738,
                        55,"000-000-000",132.86739,11.824374,
                        56,"000-BLG-929",132.78971,11.695902,
                        57,"000-BLG-930",132.850471,11.806161,
                        58,"000-BLG-931",132.868038,11.871597,
                        59,"000-BLG-932",132.811608,11.790066,
                        60,"000-BLG-934",132.892945,11.828924,
                        61,"000-000-000",132.835828,11.771293,
                        62,"000-000-000",132.872421,11.757749,
                        63,"000-BLG-935",132.936529,11.779532,
                        64,"000-BLG-936",132.815266,11.849008]

for i in range(0,64*4,4):
    m67_AUID_map.append([str(m67_orig_id_AUID_map[i]).strip(),m67_orig_id_AUID_map[i+1]]) # original Henden reference numbers and matching AUID
    
  


#########################################
#   Get Telescope id                    #
#########################################
# Retrieve Current Scope list
#  Test if Telescope Configuration file exists - if not, create
try:
    config_file = open("Photometry_Transform_Config_Data.txt","r")
except: # create file
    config_file = open("Photometry_Transform_Config_Data.txt","w")
    linetext = "Telescope_id;Add Scope;\n"  #create file with 'Add Scope" line
    config_file.write(linetext)
    config_file.close()
    config_file = open("Photometry_Transform_Config_Data.txt","r") # open newly created file for reading
tel_id_list = []  # start telescope id list
for line in config_file:
    aline = []  # hold parsed line
    lineparse(line,aline,[";",";"]) # on ; is delimiter
    if aline[0] == "Telescope_id":
        tel_id_list.append(aline[1])
config_file.close()
#  set up combobox for selection/addition
            
Label(app,text = "Select Telescope ",font=12,bg="#E0FFFF").grid(row=0,column=0,sticky = "W")
tel_id_picked_var = StringVar()
tel_id_box = ttk.Combobox(app,width=10,textvariable=tel_id_picked_var,values=tel_id_list)
tel_id_box.state(['readonly'])
tel_id_box.bind("<<ComboboxSelected>>",tel_id_pick)
tel_id_box.current(0)
tel_id_box.grid(row=0,column=1)

# Select Standards Field
linetag = "Select Standards Field - "
btn1name = "M67"
btn2name = "NGC7790"
btn3name = "M11"
btn4name = "NGC 1252"
btn5name = "NGC 3532"
btn6name = "Melotte 111"
btn7name = "Landolt Field"
line = 2
col = 0
var = StringVar()
var.set(btn1name)
SevenRadioButton(app,linetag,btn1name,btn2name,btn3name,btn4name,btn5name,btn6name,btn7name,line,col,var)


# Retrieve Format and File Name of Magnitude Measurements File
magfilenam = "No file selected"
Label(app,text="Load Instrument Magnitude File - Format?",font=12,bg="#E0FFFF").grid(row=3,columnspan=2,sticky=W,pady=10)
format_tag = ""
fmt1name = "TG / AIP4WIN"
fmt2name = "MaxIm"
fmt3name = "VPHOT - Enter Min VPhot SNR"
line_fmt = 3
col_fmt = 2
fmt_name = StringVar()
fmt_name.set(fmt1name)
# TwoRadioButton(app,format_tag,fmt1name,fmt2name,line_fmt,col_fmt,fmt_name)
Radiobutton(app,text=fmt1name,variable=fmt_name,value=fmt1name,font=12).grid(row=line_fmt,column=col_fmt,pady=5,padx=2)
Radiobutton(app,text=fmt2name,variable=fmt_name,value=fmt2name,font=12).grid(row=line_fmt,column=col_fmt+1,pady=5)
# add third button for VPHOT format
Radiobutton(app,text=fmt3name,variable=fmt_name,value="VPHOT",font=12).grid(row=line_fmt,column=col_fmt+2,pady=5,columnspan=2)
vphot_snr = Entry(app,width=4,font=12)
vphot_snr.grid(row=line_fmt,column=col_fmt+4,pady=10)
vphot_snr.delete(0,END)
vphot_snr.insert(0,"20")
Label(app,text="    Current file - ",font=12,bg="#E0FFFF").grid(row=4,column=0,sticky=E,pady=5)
filelabel = Text(app,width = 100, height = 1)
filelabel.grid(row=4,column=1,columnspan=8,sticky="W")
filelabel.delete(1.0,END)  # clear previous text
filelabel.insert(0.0,"No file selected")
getfilnamebutton = Button(app,text="Select File(s)",state = "disabled",font=12)
getfilnamebutton.grid(row=3,column=col_fmt+5,pady=10)
getfilnamebutton["command"] = get_file_name
#  Add horizontal break line

Label(app,text=("---------" * 20)).grid(row=7,column=0,columnspan=8)
            
# Create Button to calculate transforms
caltransformsbutton = Button(app,text="Calculate Transform Set")
caltransformsbutton.configure(command = calculatetransforms,state = "disabled",font=12)
caltransformsbutton.grid(row=8,column=0,columnspan=2,padx=20,pady=10)

# Create Button to save transforms - disabled
save_xform_button = Button(app,text="Save Transform Set")
save_xform_button.configure(state = "disabled", command = savetransforms,font=12)
save_xform_button.grid(row=8,column=2,padx=20)

# Create button to merge results of different observations
merge_obs_sets_button = Button(app,text="Review / Average\n Transform Sets")
merge_obs_sets_button.configure(command = mergesets,state = "disabled",font=12)
merge_obs_sets_button.grid(row=8,column=3)

# Create button to delete of transform sets
delete_obs_sets_button = Button(app,text="Delete Old \nTransform Sets")
delete_obs_sets_button.configure(command = deletesets,state = "disabled",font=12)
delete_obs_sets_button.grid(row=8,column=4)
root.mainloop()



