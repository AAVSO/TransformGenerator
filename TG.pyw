#
#   TG VERSION 6.5beta
#
import matplotlib
matplotlib.use('TkAgg')
try:
    import Tkinter
    import ScrolledText as tkst
    from Tkinter import *
    import ttk
except ImportError:
    import tkinter
    import tkinter.scrolledtext as tkst
    from tkinter import *
    from tkinter import ttk
try:
    from tkFileDialog import askopenfilenames, asksaveasfile, askopenfilename
except ImportError:
    from tkinter.filedialog import askopenfilenames, asksaveasfile, askopenfilename
import sys
import numpy as np
from scipy import stats
import matplotlib.pyplot as plt
from time import gmtime,strftime,time
import time
import pickle
try:
    from urllib2 import urlopen
except ImportError:
    from urllib.request import urlopen
from pylab import get_current_fig_manager
import json
from decimal import *
import astropy.units as u
from astropy.time import Time
from astropy.coordinates import SkyCoord, EarthLocation, AltAz
import math
try:
    import Tkinter as tk
    import tkFont
#    import ttk  # not used here
except ImportError:  # Python 3
    import tkinter as tk
    import tkinter.font as tkFont
#try:
#    # for Python2
#    import Tkinter as tk
#    import ScrolledText as tkst
#except ImportError:
#    # for Python3
#    import tkinter as tk
#    import tkinter.scrolledtext as tkst


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
#
#
#
#
#
#
#      Version 7.2
#              Since verion 6.5 - major updates
#                   Extinction Processing
#                   Testing Transforms with standard VPHOT fields
#                   Optimizing Transforms
#
#
#
#      Version 6.5
#              Add extinction support
#
#
#
#      Version 6.4
#              Add support for Landolt field
#              Fix delete transform sets (Mac issue)
#      Version 6.3
#              Add Melotte 111 field support
#              Add code to import and work on both Python 3.x and 2.7 
#      Version 6.0  
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
            global md_col_list,meas_JD,transform_names,transform_inst,num_meas_stars,transform_raw_data,fig1,tel_id
            global txtboxlab,titlab,std_field_name,transform_val_err,star_id_list,file_namelist,vphot_snr,radecwindow,enteredfield
            global radecimal,decdecimal,errflag,extinction_setting,kprime_u,kprime_b,kprime_v,kprime_r,kprime_i,kdblprime_b,kdblprime_v,kdblprime_r,kdblprime_i,ext_used
            global star_id_list,star_id_list_label,std_fields_mag,std_field_star_count,searchfield,std_field_mags,sf_col_list,detailed_print_setting

           
#
# Create transforms from instrument magnitude measurement data
#
            telescopename = tel_id # Telescope Name
            std_field_name = var.get()
#
#   Test for extinction setup
#
            config_file = open("Photometry_Transform_Config_Data.txt","r") # open telescope info file
            for line in config_file:
                aline = []  # hold parsed line
                lineparse(line,aline,[";",";"]) # on ; is delimiter
#                print("\naline, telescopename, len(aline) ",aline,telescopename, len(aline))
#                print("aline[1], telescopename,len(aline)",aline[1], telescopename,len(aline))
                if (aline[1] == telescopename) and (len(aline) == 16): # found extinction record
                    ext_aline = aline # save all telescope data including extinction, observatory location
#                    print("ext_aline, ",ext_aline)
# Format of telescope line "ext_aline" -  #  'Telescope id';ex_tel_id;k'u;k'b;k'v;k'r;k'i;k"b,k"v,k"r,k"i,;obs_lat;obs_long;obs_elev;obslatdecimal;obslongdecimal,\n

                    kprime_u = aline[2]
                    kprime_b = aline[3]
                    kprime_v = aline[4]
                    kprime_r = aline[5]
                    kprime_i = aline[6]
                    kdblprime_b = aline[7]
                    kdblprime_v = aline[8]
                    kdblprime_r = aline[9]
                    kdblprime_i = aline[10]
                    obs_lat = aline[11]
                    obs_long = aline[12]
                    obs_elev = aline[13]
                    obslatdecimal = aline[14]
                    obslongdecimal = aline[15]
                    break # valid extinction record
                elif aline[1] == telescopename : # means no extinction values set
                    ext_aline = [] # informs later logic no extinction data
                
                    
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
                            searchdec = str((abs(float(aline[1]))+float(aline[2])/60+float(aline[3])/3600))[:6]
                            if "-" in aline[1]:
                                searchdec = "-" + searchdec
                                
    
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
          
            retrieve_std_mags()
            
            
#            star_id_list = [] # start list of reference star ids - will contain AUID or Boulder ids
#            star_id_list_label = [] # start matching list to contain VPHOT/VSP label (duplicates at times...)
#            sf_col_list = ["RA","Dec","U","B","V","R","I"] # list names of each column in std_field_mags array
# Create Master Standard Field Magnitudes array
#            std_field_mags = np.zeros((500,len(sf_col_list))) # allow 500 reference stars
#
##############################################################################################
            ##################################################################################
############
##              NEW VSP API CODE TO RETIEVE STANDARD REFERENCE MAGNITUDES
#
#            try:
#                f = urlopen('https://www.aavso.org/apps/vsp/api/chart/?'+ searchfield +'&fov=210&maglimit=16.5&special=std_field&format=json')
#
#            except:
#                Errormsg("Could Not Access AAVSO Web Site")
#                return
#            chart_data = json.load(f)   # chart_data is a python dictionary
#            vsp_ref_data = chart_data.get("photometry")  # vsp_ref_data is a Python list, vsp_ref_data[i] are dictionaries
#            i = 0 # avoid error if no reference stars
#            for i in range(len(vsp_ref_data)):
#                star_id_list.append(vsp_ref_data[i].get("auid"))  # store auid
#                star_id_list_label.append(str(vsp_ref_data[i].get("label")))  # store VPHOT/VSP label - use string format to match AIP and MaxIm
#  Get, convert and save right ascension
#                line = vsp_ref_data[i].get("ra")  # set up ra parse
#                delim = [":",":"]  #  set colon parse delimeter
#                aline = []
#                lineparse(line,aline,delim)  # parse line
#                std_field_mags[i,0] = (Decimal(aline[0]) + Decimal(aline[1])/Decimal('60') + Decimal(aline[2])/Decimal(3600))*Decimal(15)  # ref star right ascension in degrees
#                print("RA - line,aline,std_field_mags[i,0]",line,aline,std_field_mags[i,0])
#  Get, convert and save declination
#               line = vsp_ref_data[i].get("dec")  # set up declination parse
#                aline = []
#                lineparse(line,aline,delim)
#                std_field_mags[i,1] = abs(Decimal(aline[0])) + Decimal(aline[1])/Decimal(60) + Decimal(aline[2])/Decimal(3600)
#                if aline[0][:1] == "-" :  # handle minus sign
#                    std_field_mags[i,1] = -std_field_mags[i,1]  # add negative sign
#                print("Dec - line,aline,std_field_mags[i,1]",line,aline,std_field_mags[i,1])
#  Get and save standard star reference magnitudes     
#                band_meas = vsp_ref_data[i].get("bands")  # get list of photometry reference values - each entry is a dictionary
#                bandmapping = ["","","U","B","V","Rc","Ic"]  # .index will provide index for std_field_mags
#                std_field_mags[i,bandmapping.index("U")] = -1000 # set to no data in case no U value provided
#                for j in range(len(band_meas)):
#                    if band_meas[j].get("band") in bandmapping:  # look out for new bands being added
#                        std_field_mags[i,bandmapping.index(band_meas[j].get("band"))] = band_meas[j].get("mag")
#                
#                
#            std_field_star_count = i + 1
#           if std_field_star_count < 3 :
#                Errormsg("Less than 3 Reference Stars - Abort Calculations")
#                return            
            
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
#            for i in range(len(star_id_list)):
#                print("\ni,star_id_list[i],std_field_mags(i,) = ",i,star_id_list[i],std_field_mags[i,])            
            
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
#
#
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
                if len(file_namelist) < 2 :
                    Errormsg("Need at least two filters data to create transforms")
                    return
# Read and process first VPHOT file
                snr_limit = float(vphot_snr.get())
                vphot_filt_list = []
                vphot_star_id = []
                for i in range(500):  # nax number of vphot comps allowed is 500 minus the number of old Boulder ids - added later
                    vphot_star_id.append(" ")    # create array with vphot id's tied to AUID  (star_id_list)
                vphot_col_list = ["Vphot_Star_id","IM","SNR","X","Y","Sky","Air","B-V","Ref-mag","Target estimate","Active"]
                mmm_obs_count_col_list = ["Star_id_index","u","b","v","r","i"]
                mmm_obs_count = np.zeros((500,len(mmm_obs_count_col_list))) # Create array to count number of measurements for each filter - for averaging
                srow = 0 # initialize index of last row with valid data in measured_machine_mags array
                star_id_not_matched_list = "" 
                one_msg_line = ""
                mmm_data_started = "N"                
                pbar_ext = ttk.Progressbar(app,orient = 'horizontal',length = 200, mode = "determinate",maximum = len(file_namelist)) # progress bar for transformation
                pbar_ext.grid(row=12,column=5,sticky="NESW")

                for file_i in range(len(file_namelist)): # process each file listed
#                    print("\n\n\n\n****************************************************************************************************")
 #                   print("file_i = ",file_i)
                    measurements = open(file_namelist[file_i],mode="r")  # retrieve instrument measurements file
                    starline_found = "N"
                    activestars = 0 # set to count active stars to ensure some found 
                    for oneline in measurements: # process each line in the file
#                        print("oneline in measurements - ",oneline)
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
                                starline_found = "Y"
                            
                            continue  # done looking at header lines - most ignored
#
# Start processing lines of measurement data following "Star" line
#
                        else:  # process measurement lines
                            
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
                                     break # found match - go to next line
                                
                                continue # search next standard line to find match
                    num_meas_stars = srow + 1 # total number of stars with measurements

#
################################################################################################################################################################
#
#      If requested, apply extinction to VPHOT instrument magnitudes here for each file
#
#
#                   Test if extinction requested
#                    print("Entry extinction_setting = ",extinction_setting.get())
                    ext_used = "No"
                    if extinction_setting.get() == "Y" : 
                        if meas_JD == str(100000):
                            Errormsg("No JD observation date in file - extinction can not be calculated. \nTransforms will be computed without extinction.")
                        elif len(ext_aline) == 0 : # no extinction data for this telescope
                            Errormsg("No extinction settings for this telescope")
                            extinction_setting.set("N")
                        else: # Apply Extinction
                            
#
# mmm_col_lst = ["Star_id_index","RA","Dec","u","b","v","r","i"]
# sf_col_list = ["RA","Dec","U","B","V","R","I"] # list names of each column in std_field_mags array
# filtlist = ["u","b","v","r","i"]
#  First, insert RA/Dec for each star into measured_machine_mags                                                                   #
                                            
                            ext_used = "Yes"
                            for i in range(num_meas_stars):
                                star_id_ref = int(measured_machine_mags[i,mmm_col_lst.index("Star_id_index")])
                                measured_machine_mags[i,mmm_col_lst.index("RA")] = std_field_mags[star_id_ref,sf_col_list.index("RA")]
                                measured_machine_mags[i,mmm_col_lst.index("Dec")] = std_field_mags[star_id_ref,sf_col_list.index("Dec")]
#  Adjust instrument magnitudes for this VPHOT file i.e. one filter with one time of observation
                            first_order_list = [kprime_u,kprime_b,kprime_v,kprime_r,kprime_i]
                            second_order_list = [0,kdblprime_b,kdblprime_v,kdblprime_r,kdblprime_i] # first zero for kdblprime_u which by definition is zero (not sure why...)
                            filtlist = ["u","b","v","r","i"]
#                         
# Format of telescope line "ext_aline" -  #  'Telescope id';ex_tel_id;k'u;k'b;k'v;k'r;k'i;k"b,k"v,k"r,k"i,;obs_lat;obs_long;obs_elev;obslatdecimal;obslongdecimal,\n

                            obs_lat_float_decimal = float(obslatdecimal)
                            obs_long_float_decimal = float(obslongdecimal)
                            obs_elev_float = float(obs_elev)
                            obs_location = EarthLocation(lat=obs_lat_float_decimal*u.deg, lon=obs_long_float_decimal*u.deg, height=obs_elev_float*u.m)
                            if detailed_print_setting.get() == "Y":
                                print(50*"*" + "  VPHOT Load in Generating Transforms logic - Extinction Application - calculatetransforms()\n")
                            for i in range(num_meas_stars):
                                star_AUID_index = int(measured_machine_mags[i,mmm_col_lst.index("Star_id_index")])
                                if detailed_print_setting.get() == "Y":
                                    print("\nStar AUID - ",star_id_list[star_AUID_index])
                                star_coord = (SkyCoord(measured_machine_mags[i,mmm_col_lst.index("RA")],
                                              measured_machine_mags[i,mmm_col_lst.index("Dec")], unit = "deg"))
                                meas_JD_float = float(meas_JD)
                                t = Time(val = meas_JD_float, format='jd' )
                                star_loc  = star_coord.transform_to(AltAz(obstime=t,location=obs_location))
                                airmass = star_loc.secz
                                mmm_filt_index = mmm_col_lst.index(currentfilter.lower()) # index in mmm array
                                if detailed_print_setting.get() == "Y":
                                    print("\ncurrentfilter, filt_index , filt = ",currentfilter, mmm_filt_index,filtlist[mmm_filt_index-3])
                                
                                if measured_machine_mags[i,mmm_filt_index] != 0 and measured_machine_mags[i,mmm_filt_index] != -1000 : # skip empty cells and FAlSE stars
                                    measured_machine_mags[i,mmm_filt_index] -= airmass*first_order_list[mmm_filt_index-3]  # apply extinction, note offset of 4 between ext_aline and mmm_col_list
                                    if detailed_print_setting.get() == "Y":
                                        print("airmass*first_order_list[mmm_filt_index-3] = ",airmass*first_order_list[mmm_filt_index-3])
                                    if currentfilter.lower() != "i" :  # no second order filter correction for i possible
                                        if detailed_print_setting.get() == "Y":
                                            print("\n2nd order terms,airmass,second_order_list[mmm_filt_index-3],std_field_mags[star_AUID_index,mmm_filt_index-2],std_field_mags[star_AUID_index,mmm_filt_index-1]\n",(
                                                airmass,second_order_list[mmm_filt_index-3],std_field_mags[star_AUID_index,mmm_filt_index-1],std_field_mags[star_AUID_index,mmm_filt_index]))
                                        measured_machine_mags[i,mmm_filt_index] -= airmass*second_order_list[mmm_filt_index-3]*(
                                            std_field_mags[star_AUID_index,mmm_filt_index-1] - std_field_mags[star_AUID_index,mmm_filt_index])
#      progress bar status
                    pbar_ext.step(amount = 1)
                    root.update()
                    time.sleep(0.5)
                pbar_ext.destroy()

#        End of extinction application                        
#                                                   
################################################################################################################################################################                
                if star_id_not_matched_list != "":
                    Errormsg("Reference Star ids not found in VSP -\n" + star_id_not_matched_list + one_msg_line + "\nStars Excluded from Calculation")
                if activestars < 2:
                    Errormsg("Less than two active stars in VPhot File")
                    return
#
# Search all magnnitudes and set any 0 to -1000 indicating no measurement or bad measurement
# mmm_col_lst = ["Star_id_index","RA","Dec","u","b","v","r","i"]
#
                for i in range(num_meas_stars):
                    for j in range(3,8):
                        if measured_machine_mags[i,j] == 0:
                            measured_machine_mags[i,j] = -1000



##################################################################################################################################
##################################################################################################################################
#
                                
                                
                        
                    
                    
                
# For each star, compute airmass
                    
##################################################################################################################################
##################################################################################################################################
#                for i in range (num_meas_stars+2):
#                    print("\ni, measured_machine_mags[i,] = ",i, measured_machine_mags[i,])
                                   

        
                                 
            config_file.close()  # Close Photometry Transform Coniguration Data file
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
            md_col_list = ["Star_id_index","RA","Dec","U-B","B-V","V-R","R-I","U-u","B-b","V-v","R-r","I-i","u-b","b-v","v-r","r-i","V-I","v-i"]
            md = np.zeros((num_meas_stars,len(md_col_list))) # magnitude differences array
            for i in range(num_meas_stars):
                md[i,md_col_list.index("Star_id_index")] = measured_machine_mags[i,mmm_col_lst.index("Star_id_index")] # Star id index number
                j = int(md[i,md_col_list.index("Star_id_index")])  # Star id index number
                md[i,md_col_list.index("RA")] = std_field_mags[j,sf_col_list.index("RA")]
                md[i,md_col_list.index("Dec")] = std_field_mags[j,sf_col_list.index("Dec")]
                md[i,md_col_list.index("U-B")] = std_field_mags[j,sf_col_list.index("U")] - std_field_mags[j,sf_col_list.index("B")]
                md[i,md_col_list.index("B-V")] = std_field_mags[j,sf_col_list.index("B")] - std_field_mags[j,sf_col_list.index("V")]
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
                                       
# Create list of instructions to generate transforms - list element sequence is  - transform, x values, y values,(Y/N inverse indicator)
            transform_inst = ["Tub","U-B","u-b","Y","Tbv","B-V","b-v","Y","Tvr","V-R","v-r","Y",
                       "Tri","R-I","r-i","Y","Tu_ub","U-B","U-u","N","Tb_ub","U-B","B-b","N",
                       "Tb_bv","B-V","B-b","N","Tv_bv","B-V","V-v","N","Tv_vr","V-R","V-v","N",
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
            if ext_used == "Yes" :
                line2 = "    Extinction Applied"
            elif ext_used == "No":
                line2 = "   Extinction Not Used"
            else:
                Errormsg("Extinction coding error")
            tittext = ["    Transform Values\n" + line2,lab_text,"  Select Transforms for\n   Review and Analysis"]
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
                txtboxlab.append(Text(app,width=40,height=1))
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
    fig1 = plt.figure(1)  # start figure 1
##
##  Add test code to raise window to front
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
    if i<=j and i != len(line): # check field to right of last delimiter for content 
        temp = line[i:].strip()
        if temp != "":
            linelist.append(temp)
   

########################################################
########################################################
#                                                      #
#  Retrieve Standard Star Magnitudes Routine           #
#                                                      #
#                                                      #
########################################################
########################################################
def retrieve_std_mags():
    global star_id_list,star_id_list_label,std_field_mags,std_field_star_count,searchfield,sf_col_list
    
           
# Retrieve Standard Field File 
      
    star_id_list = [] # start list of reference star ids - will contain AUID or Boulder ids
    star_id_list_label = [] # start matching list to contain VPHOT/VSP label (duplicates at times...)
    sf_col_list = ["RA","Dec","U","B","V","R","I","Uerr","Berr","Verr","Rerr","Ierr"] # list names of each column in std_field_mags array
# Create Master Standard Field Magnitudes array
    std_field_mags = np.zeros((500,len(sf_col_list))) # allow 500 reference stars

##############################################################################################
##################################################################################
############
##              NEW VSP API CODE TO RETIEVE STANDARD REFERENCE MAGNITUDES
#
    try:
        f = urlopen('https://www.aavso.org/apps/vsp/api/chart/?'+ searchfield +'&fov=210&maglimit=16.5&special=std_field&format=json')

    except:
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
        std_field_mags[i,1] = abs(Decimal(aline[0])) + Decimal(aline[1])/Decimal(60) + Decimal(aline[2])/Decimal(3600)
        if aline[0][:1] == "-" :  # handle minus sign
            std_field_mags[i,1] = -std_field_mags[i,1]  # add negative sign
#                print("Dec - line,aline,std_field_mags[i,1]",line,aline,std_field_mags[i,1])
#  Get and save standard star reference magnitudes     
        band_meas = vsp_ref_data[i].get("bands")  # get list of photometry reference values - each entry is a dictionary
        bandmapping = ["","","U","B","V","Rc","Ic"]  # .index will provide index for std_field_mags
        std_field_mags[i,bandmapping.index("U")] = -1000 # set to no data in case no U value provided
        for j in range(len(band_meas)):
            if band_meas[j].get("band") in bandmapping:  # look out for new bands being added
                std_field_mags[i,bandmapping.index(band_meas[j].get("band"))] = band_meas[j].get("mag")
# mag error is offset by 5 from mags - i.e. column for magerror = column for mag + 5 for every filter
                std_field_mags[i,bandmapping.index(band_meas[j].get("band")) + 5] = band_meas[j].get("error")
        
    std_field_star_count = i + 1
    if std_field_star_count < 3 :
        Errormsg("Less than 3 Reference Stars - Abort Calculations")
        return            

#####################################################################################################
#####################################################################################################
#
#
#                  End of Standard Reference Mag retrieval routine
#
#####################################################################################################
#####################################################################################################
# Create Get File Name button method        #
#############################################

def get_file_name():
    global magfilenam,tel_id,caltransformsbutton,titlab,filelabel,file_namelist
    if tel_id == "Add Scope":
        Errormsg("Select Telescope Name first")
    else:
        fn = askopenfilenames(title = "Select Instrument Measurements File(s)") # may be multiple files if VPHOT
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
    test_transform_set_button.configure(state = "active", activebackground = "#E0FFFF",bg="#E0FFFF")
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
    msg = savetransforms_1()
    MessageBox(msg + "\n")
    return


def savetransforms_1():
    global transform_names,transform_val,transform_val_err,transform_val_r2,meas_JD,tel_id,std_field_name,ext_used
    curtime = strftime("%Y%m%d%H%M%S",gmtime())
    record = [tel_id,meas_JD,curtime,transform_names,transform_val,transform_val_err,transform_val_r2,std_field_name,ext_used]
#    print("len(record), record = ",len(record),record)
    transform_file = open("transform_values.ptgp","ab")
    pickle.dump(record,transform_file)
    transform_file.close()
    msgtxt = "Transforms saved on Review/Average Page \nat UT  " +curtime[0:4] + "-" + curtime[4:6] + "-" + curtime[6:8] + "  " + curtime[8:10] +":" + curtime[10:12] + ":" + curtime[12:]
    return msgtxt

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
    # size window
    w, h = root.winfo_screenwidth(), root.winfo_screenheight()
    mergewindow.geometry("%dx%d+0+0" % (.9*w, .8*h))
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
#    transform_file = codecs.open('transform_values.ptgp', encoding='utf-8'):
#    print("transform_file ", transform_file)
    count = 0  # set count of number of records for telescope
    for i in range(1000):  # get all records for selected telescope
        try:
            record = pickle.load(transform_file)
#             print("record=",record)
#            print("\nlen(record),record[len(record)-1] = ",len(record),record[len(record)-1])
            if record[0] == tel_id:
                if len(record) == 8:  # this i an old version record before extinction added
                    record.append("No") # Indicate old version had no extinction applied

                tel_id_saved_xforms.append(record)
                count = count + 1
        except Exception as e:
            print("Error Code = ",e)
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
        Label(root2,text="Extinction Applied?",font="10").grid(row=7,column=2,columnspan=2,sticky="E")
        table_start_row=1
        for i in range(len(allxforms)):  # display list of all possible transforms
            Label(root2,text=(allxforms[i] + " "),font="9").grid(row=table_start_row+7+i,column=3,sticky="E")
        remove_col = "N"  # indicate not removing columns
        for i in  range(len(obs_selected)):
            Obs_Set_Columns(root2,(table_start_row+1),(i+4),obs_selected[i]) # Display each column of data
        if len(prev_obs_selected) > len(obs_selected):  # check if previously more columns displayed, if so, remove
            remove_col = "Y"
            for i in range(len(obs_selected),len(prev_obs_selected)):
                dummy = 0  # only so remove process will work - not actually used
                Obs_Set_Columns(root2,(table_start_row+1),(i+4),dummy)
        avg_selected_observations = Button(root2,text = "Compute Average of Checked Transform Sets",command = avg_sets,font=10,bg="#E0FFFF").grid(row=24,column=4,columnspan=10)
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
def ra_dec_validate(ra,dec):
    global radecimal,decdecimal,errflag,fmt_type
#
#  Ensure valid Right Ascension / Declination inputs
# Validate text input as xxx.xx , DD:MM:SS or HH:MM:SS
#   errflag = 0 if valid, -1 if invalid ra,  -2 if invalid dec
#   fmt_type = 1 if decimal, 2 if colon format (HH:MM:SS or DD:MM:SS), 3 if invalid
#
    fmt_type = 3 # initialize as invalid format - change if all tests passed
#
# Test Right Ascension Input    
    
    
    if ra.find(":") > 0 : # if colon found assume HH:MM:SS format
        aline = [] # create holding list for parsed oneline
        delim = [":",":"]  # colon delimeter
        if ra[len(ra)-1:] == ":" : # check is user left final field empty
            ra = ra + "00" # enter zero value
        lineparse(ra,aline,delim)
        for i in range(0,3) :
            if aline[i] == "" :
                aline[i] = "00"
        if len(aline) != 3:
            errflag = -1
            return -1
        try:
            if float(aline[0]) >= 24 or float(aline[1]) >= 60 or float(aline[2]) >= 60  or float(aline[0]) <0 :
                errflag = -1
                return -1
            else:
                ra_float = np.sign(float(aline[0]))*(15*(abs(float(aline[0]) + float(aline[1])/60 + float(aline[2])/3600)))
                radecimal = str(ra_float)[:7]
        except:
            errflag = -1
            return
        fmt_type = 2
        
    else:  # should be DDD.DD
        try:
            if float(ra) > 360 or float(ra) < -180:
                errflag = -1
                return errflag
        except:
            errflag = -1
            return errflag
        radecimal = ra
        fmt_type = 1
        
    
#
# Test Declination Input
#
    if dec.find(":") > 0 : # if colon found assume DD:MM:SS
        aline = [] # parse holding list
        delim = [":",":"] # colon delimeter
        if dec[len(dec)-1:] == ":" : # check for last field left empty
            dec = dec + "00" # enter zero value
        lineparse(dec,aline,delim)
        for i in range(0,3) :
            if aline[i] == "" :
                aline[i] = "00"
        if len(aline) != 3:
            errflag = -2
            return errflag
        try:
            if abs(float(aline[0]) >= 90) or float(aline[1]) > 60 or float(aline[2]) >60 :
                errflag = -1
                return errflag
        except:
            errflag = -2
            return errflag
        fmt_type = 2
        decdecimal = str(float(aline[0]) + float(aline[1])/60 + float(aline[2])/3600)[:6] 
        
    else:  # should be DD.DD
        try:
            if abs(float(dec)) > 90 :
                errflag = -2
                return errflag
        except:
            errflag = -2
            return errflag
        fmt_type = 1
        decdecimal = dec
#
#  All tests passed
#
    errflag = 0
    return errflag
        
#
#  END OF RA/DEC of format review
#

        
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
    global raentry,decentry,radecwindow,enteredfield,radecimal,decdecimal,errflag,fmt_type
    rainput = raentry.get()
    decinput = decentry.get()
    ra_dec_validate(rainput,decinput)
    if errflag == 0 :
        enteredfield = "ra="+ radecimal + "&dec="+ decdecimal
    else:
        if errflag == -1:
            Errormsg("Invalid Right Ascension")
        else:
            Errormsg("Invalid Declination")
        return
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
# Add code showing if extinction applied
        self.te = Text(master,width = 3,height=1)
        self.te.grid(row=boxrow+5,column=boxcol,pady=3)
        self.ext_used = self.record[8]
        self.te.insert(0.0,self.ext_used)
#
#  NEED FIX - OLDER VERSIONS DON'T HAVE         
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
            self.t4.grid(row= boxrow + 6 + i, column = boxcol)
            
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
        t4.grid(row=8+i,column=12)
    Label(root2,text="Avg Transform",bg="yellow").grid(row=3,column=12)

# Add Button to allow saving of average transforms
    save_xforms_btn = Button(root2,text = "Save File of Average Transforms\nEnter/Select File Name\n",command = export_transforms,font=10,bg="#E0FFFF").grid(row=25,column=4,columnspan=10)

################################################################################
#                                                                              #
#    Create Export File of Averaged Transforms                                 #
#                                                                              #
################################################################################


def export_transforms():
    msg = export_transforms_1(root2)
    MessageBox(msg)
    return


def export_transforms_1(parentname):
    global xforms_txt,allxforms,tel_id,output_file_xform_val_list,output_file_xform_err_list,output_file_xform_r2_list
    export_file = asksaveasfile(mode="w",defaultextension = ".ini",
                                title = "Enter Name of Export File", parent = parentname)
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
    msg = "Transforms for Telescope " + tel_id + "\nSaved at UT\n" + curtime + " to file\n" + fname
    return msg
    
######################################################################
######################################################################
##                                                                  ##
##          Create Extinction Settings Window for input of          ##
##        extinction coefficients and observing site lat/long       ##
##                                                                  ##
######################################################################
######################################################################

def save_extinction():
    global extinctwindow
    global ex_tel_id_box,ex_tel_id,kprime_u,kprime_b,kprime_v,kprime_r,kprime_i,kdblprim_b,kdblprim_v,kdblprim_r,kdblprim_i,obs_lat,obs_long,obs_elev
    global radecimal,decdecimal,errflag,fmt_type
#
#  Validate lat/long input
#
    latentered = obs_lat.get()
    lat = latentered
    if "n" in latentered or "N" in latentered or "S" in latentered or "s" in latentered :  # N/n/S/s found
        lat  = latentered[:len(latentered)-1] # remove N/n/S/s
    aline = []
    if ":" in lat : 
        lineparse(lat,aline,[":",":"])
    else:
        aline.append(lat) # set aline[0]
    if len(aline) == 3  :  # assume xxx:xx:xx format
        try:
            obslatfloat = abs(float(aline[0]) + float(aline[1])/60 + float(aline[2])/3600)
            if obslatfloat > 90 :
                Errormsg("Latitude Format Error")
                return
            obslatdecimal = str(obslatfloat)[:7]
            if "s" in latentered or "S" in latentered or float(aline[0]) < 0 :
                obslatdecimal = "-" + obslatdecimal
        except:
            Errormsg("Latitude Format Error")
            return
#####
#  assuming latitude is +/- DD.DDD
#
    else:
        try:
            obslatfloat = abs(float(lat))
            if obslatfloat > 90 :
                Errormsg("Latitude Format Error")
                return
            obslatdecimal = str(obslatfloat)[:7]
            if "s" in latentered or "S" in latentered or float(aline[0]) < 0 :
                obslatdecimal = "-" + obslatdecimal
        except:
            Errormsg("Latitude Format Error")
            return
        
#
# Validate longitude
#
    longentered = obs_long.get()
    long = longentered
    if "W" in longentered or "w" in longentered or "E" in longentered or "e" in longentered :
        long = longentered[:len(longentered)-1] # assumes last character - remove
    aline = []
    lineparse(long,aline,[":",":"])
    if len(aline) == 3 : # assume DDD:MM:SS format
        try:
            obslongfloat = abs(float(aline[0])) + float(aline[1])/60 + float(aline[2])/3600
        except:
            Errormsg("Longitude Format Error")
            return
    else:  # assuming DDD.DDD format
        try:
            obslongfloat = abs(float(long))
        except:
            Errormsg("Longitude Format Error")
            return
    if obslongfloat < -180 or obslongfloat > 360 :
        Errormsg("Longitude Format Error:")
        return
    obslongdecimal = str(obslongfloat)[:8]
    if "W" in longentered or "w" in longentered or float(aline[0]) < 0 :
        obslongdecimal = "-" + obslongdecimal
    config_file = open("Photometry_Transform_Config_Data.txt","r")
    outputline = []
    for line in config_file: # read each line
        aline = []
        lineparse(line,aline,[";",";"])
        if aline[1] != ex_tel_id : # if not current scope data, write existing data into output file
            outputline.append(line)
            continue
        newline = ("Telescope_id;" + ex_tel_id + ";" + kprime_u.get() + ";" + kprime_b.get() + ";" +kprime_v.get() + ";" +kprime_r.get() + ";" 
            + kprime_i.get() + ";" + kdblprim_b.get() + ";" + kdblprim_v.get() + ";" + kdblprim_r.get() + ";" + kdblprim_i.get() + ";" + obs_lat.get() + ";" + obs_long.get() + ";" + obs_elev.get() + ";" +
            obslatdecimal + ";" + obslongdecimal + ";\n")
        outputline.append(newline)
    config_file.close()
    config_file = open("Photometry_Transform_Config_Data.txt","w")
    config_file.writelines(outputline)
    config_file.close()
    MessageBox("Extinction Values Saved for " + ex_tel_id + "\nBe certain to reload VPHOT files if testing transform coefficients")
    extinctwindow.destroy()
    


def ex_tel_id_pick(event):
    global ex_tel_id_box,ex_tel_id,kprime_u,kprime_b,kprime_v,kprime_r,kprime_i,kdblprim_b,kdblprim_v,kdblprim_r,kdblprim_i,obs_lat,obs_long,obs_elev
    ex_tel_id = ex_tel_id_box.get()
    config_file = open("Photometry_Transform_Config_Data.txt","r") # open file for reading
    for line in config_file:
        aline = []  # hold parsed line
        lineparse(line,aline,[";",";"]) # on ; is delimiter
#
#  Format of line:
#        newline = ("Telescope_id;" + ex_tel_id + ";" + kprime_u.get() + ";" + kprime_b.get() + ";" +kprime_v.get() + ";" +kprime_r.get() + ";" 
#            + kprime_i.get() + ";" + kdblprim_b.get() + ";" + obslat.get() + ";" + obslong.get() + ";" + 
#            obslatdecimal + ";" + obslongdecimal + ";\n")
#
#  'Telescope id';ex_tel_id;k'u;k'b;k'v;k'r;k'i;k"bbv;obs_lat;obs_long;obs_elev;obslatdecimal;obslongdecimal;n
#
#  Initialize with previous values or defaults
#
        if aline[1] == ex_tel_id:
            if len(aline) == 2 or len(aline) == 13 :  # extinction data not present or set before additiona k" -  set defaults
                kprime_u.delete(0,END)
                kprime_u.insert(0,"0.6")
                kprime_b.delete(0,END)
                kprime_b.insert(0,"0.4")
                kprime_v.delete(0,END)
                kprime_v.insert(0,"0.2")
                kprime_r.delete(0,END)
                kprime_r.insert(0,"0.1")
                kprime_i.delete(0,END)
                kprime_i.insert(0,"0.08")
                kdblprim_b.delete(0,END)
                kdblprim_b.insert(0,"0.01")
                kdblprim_v.delete(0,END)
                kdblprim_v.insert(0,"0.00")
                kdblprim_r.delete(0,END)
                kdblprim_r.insert(0,"0.00")
                kdblprim_i.delete(0,END)
                kdblprim_i.insert(0,"0.00")
                obs_lat.delete(0,END)
                obs_long.delete(0,END)
                obs_elev.delete(0,END)
                obs_elev.insert(0,"0")
                if len(aline) == 13: # if previous file without all k", restore lat/long/elev
                    obs_lat.insert(0,aline[8])
                    obs_long.insert(0,aline[9])
                    obs_elev.insert(0,aline[10])
                
            else:
                kprime_u.delete(0,END)
                kprime_u.insert(0,aline[2])
                kprime_b.delete(0,END)
                kprime_b.insert(0,aline[3])
                kprime_v.delete(0,END)
                kprime_v.insert(0,aline[4])
                kprime_r.delete(0,END)
                kprime_r.insert(0,aline[5])
                kprime_i.delete(0,END)
                kprime_i.insert(0,aline[6])
                kdblprim_b.delete(0,END)
                kdblprim_b.insert(0,aline[7])
                kdblprim_v.delete(0,END)
                kdblprim_v.insert(0,aline[8])
                kdblprim_r.delete(0,END)
                kdblprim_r.insert(0,aline[9])
                kdblprim_i.delete(0,END)
                kdblprim_i.insert(0,aline[10])
                obs_lat.delete(0,END)
                obs_lat.insert(0,aline[11])
                obs_long.delete(0,END)
                obs_long.insert(0,aline[12])
                obs_elev.delete(0,END)
                obs_elev.insert(0,aline[13])
                
    return

def extinction():
    global ex_tel_id_box, extinctwindow, kprime_u,kprime_b,kprime_v,kprime_r,kprime_i,kdblprim_b,kdblprim_v,kdblprim_r,kdblprim_i,obs_lat,obs_long,obs_elev,extinction_setting
    extinctwindow = Toplevel()
    extinctwindow.title("Set Up Exinction - " + version)
    try:
        config_file = open("Photometry_Transform_Config_Data.txt","r") # open file for reading
    except:
        Errormsg("Enter new telescope name on main menu")
    ex_tel_id_list = []  # start telescope id list
    for line in config_file:
        aline = []  # hold parsed line
        lineparse(line,aline,[";",";"]) # on ; is delimiter
        if (aline[1] != "Add Scope"):
            ex_tel_id_list.append(aline[1])
    config_file.close()
#  set up combobox for selection/addition
            
    Label(extinctwindow,text = "Select Telescope ",font=12,bg="#E0FFFF").grid(row=0,column=0,sticky = "W")
    ex_tel_id_picked_var = StringVar()
    ex_tel_id_box = ttk.Combobox(extinctwindow,width=10,textvariable=ex_tel_id_picked_var,values=ex_tel_id_list)
    ex_tel_id_box.state(['readonly'])
    ex_tel_id_box.bind("<<ComboboxSelected>>",ex_tel_id_pick)
    ex_tel_id_box.current(0)
    ex_tel_id_box.grid(row=0,column=1)
    Label(extinctwindow, text = "Enter First Order Extinction Coefficients:",font = 12).grid(row=1,column=0,columnspan=2,sticky = "W")
    Label(extinctwindow, text = "k'u = ",font = 12).grid(row=2,column=0,sticky = "E")
    kprime_u = Entry(extinctwindow,font=12)
    kprime_u.grid(row=2,column=1,sticky = "W")
    
    Label(extinctwindow, text = "  (Default = 0.6)", font = 12).grid(row = 2, column = 2, sticky = "W")
    Label(extinctwindow, text = "k'b = ",font = 12).grid(row=3,column=0,sticky = "E")
    kprime_b = Entry(extinctwindow,font=12)
    kprime_b.grid(row=3,column=1,sticky = "W")
    
    Label(extinctwindow, text = "  (Default = 0.4)", font = 12).grid(row = 3, column = 2, sticky = "W")
    Label(extinctwindow, text = "k'v = ",font = 12).grid(row=4,column=0,sticky = "E")
    kprime_v = Entry(extinctwindow,font=12)
    kprime_v.grid(row=4,column=1,sticky = "W")
    
    Label(extinctwindow, text = "  (Default = 0.2)", font = 12).grid(row = 4, column = 2, sticky = "W")
    Label(extinctwindow, text = "k'r = ",font = 12).grid(row=5,column=0,sticky = "E")
    kprime_r = Entry(extinctwindow,font=12)
    kprime_r.grid(row=5,column=1,sticky = "W")        
    Label(extinctwindow, text = "  (Default = 0.1)", font = 12).grid(row = 5, column = 2, sticky = "W")
    Label(extinctwindow, text = "k'i = ",font = 12).grid(row=6,column=0,sticky = "E")
    kprime_i = Entry(extinctwindow,font=12)
    kprime_i.grid(row=6,column=1,sticky = "W")
    Label(extinctwindow, text = "  (Default = 0.08)", font = 12).grid(row = 6, column = 2, sticky = "W")
    Label(extinctwindow, text = " ", font = 12).grid(row=7,column=0)
    Label(extinctwindow, text = "Enter Second Order Extinction Coefficients",font=12).grid(row=8,column=0,columnspan=2, sticky = "W")
    Label(extinctwindow, text = " ", font = 12).grid(row=9,column=0)
    Label(extinctwindow, text = 'k"b = ',font = 12).grid(row=10,column=0,sticky = "E") 
    kdblprim_b = Entry(extinctwindow,font=12)
    kdblprim_b.grid(row=10,column=1,sticky = "W")
    Label(extinctwindow, text = "  (Default = 0.01)", font = 12).grid(row = 10, column = 2, sticky = "W")
    Label(extinctwindow, text = 'k"v = ',font = 12).grid(row=11,column=0,sticky = "E") 
    kdblprim_v = Entry(extinctwindow,font=12)
    kdblprim_v.grid(row=11,column=1,sticky = "W")    
    Label(extinctwindow, text = "  (Default = 0.00)", font = 12).grid(row = 11, column = 2, sticky = "W")
    Label(extinctwindow, text = 'k"r = ',font = 12).grid(row=12,column=0,sticky = "E") 
    kdblprim_r = Entry(extinctwindow,font=12)
    kdblprim_r.grid(row=12,column=1,sticky = "W")    
    Label(extinctwindow, text = "  (Default = 0.00)", font = 12).grid(row = 12, column = 2, sticky = "W")
    Label(extinctwindow, text = 'k"i = ',font = 12).grid(row=13,column=0,sticky = "E") 
    kdblprim_i = Entry(extinctwindow,font=12)
    kdblprim_i.grid(row=13,column=1,sticky = "W")   
    Label(extinctwindow, text = "  (Default = 0.00)", font = 12).grid(row = 13, column = 2, sticky = "W")
    Label(extinctwindow, text = "Enter Location of Observatory", font = 12).grid(row=14,column =0, columnspan=2, sticky = "W")
    Label(extinctwindow, text = "Latitude (+/- DD.DDD or DD:MM:SS N/S)",font = 12).grid(row=15,column=0,columnspan=2, sticky = "E")
    obs_lat = Entry(extinctwindow, font = 12)
    obs_lat.grid(row = 15, column = 2, sticky = "W")
    Label(extinctwindow, text = "Longitude (+/- DDD.DDD or DD:MM:SS E/W)",font = 12).grid(row = 16, column = 0, columnspan=2, sticky = "E")
    obs_long = Entry(extinctwindow, font = 12)
    obs_long.grid(row = 16, column = 2, sticky = "W")
    Label(extinctwindow, text = "Elevation (meters)", font = 12).grid(row=17,column = 0, columnspan=2, sticky = "E")
    obs_elev = Entry(extinctwindow,font = 12)
    obs_elev.grid(row = 17, column = 2, sticky = "W")
    Label(extinctwindow, text = " ").grid(row = 18)
    Button(extinctwindow, text = "Save Extinction Values",command = save_extinction,font=12).grid(row=19,column=1)
    Label(extinctwindow, text = "     ", font = 12).grid(row = 20, column = 3)
    
    
#    raLabel = Label(extinctwindow,text=("RA (HH:MM:SS or DDD.xxx)"),font = 12).grid(row=1,column=0)
#    raentry = Entry(extinctwindow,font=12)
#    raentry.grid(row=1,column=1)
#    decLabel = Label(radecwindow,text=("Dec (+/-DD:MM:SS or DD.xxx)"),font=12).grid(row=2,column=0)
#    decentry = Entry(radecwindow,font=12)
#    decentry.grid(row=2,column=1)
#    Button(radecwindow,text="Enter",command = quitra,font="12").grid(row=3,columnspan=2)print("Extinction Code")
    return


############################################################################################################
############################################################################################################
##
##    Test Transforms Program                                                                             ##
##                                                                                                        ##
############################################################################################################
############################################################################################################

############################################################################################################
#                                                                                                          #
#                    Create Set of Optimized Transforms                                                    #
#                                                                                                          #
############################################################################################################
    
# save optimized transforms both internally and export file

def save_opt_xforms():
    global transform_names,transform_val,transform_val_err,transform_val_r2,meas_JD,tel_id,std_field_name,ext_used # from savetransforms function
    global allxforms, status_box,test_xforms_str,test_xforms_err_str,loaderr # from loadsave_typedtransforms function
    global best_xform_results, coef_being_optimized,status_box,save_opt_btn,output_file_xform_val_list,output_file_xform_err_list,output_file_xform_r2_list,msgwindow,transformtest
    transform_names = []
    transform_val = []
    transform_val_err = []
    transform_val_r2 = []
    for j in range(len(coef_being_optimized)) :  # saving internal reacord of transforms
        transform_names.append(coef_being_optimized[j])
        transform_val.append(best_xform_results[j,0])
        transform_val_err.append(best_xform_results[j,1])
        transform_val_r2.append(999999.) # indicate no r squared possible
    ext_used = "No"  # for now until extinction option added
    msg = savetransforms_1() # saves internal copy for use on Review/Average Page
    status_box.insert("end",msg + "\n")
    status_box.see("end")
#  set up save of TA ini file
    output_file_xform_val_list = [] # start list to save lines of transform values
    output_file_xform_err_list = [] # start list to save lines of tranform value errors
    output_file_xform_r2_list = [] # start list to save lines of transform r squared values
    for j in range(len(coef_being_optimized)):
# output file data save
        line = coef_being_optimized[j] + "= %5.3f" %  best_xform_results[j,0] # transform value line
        output_file_xform_val_list.append(line)
        line = coef_being_optimized[j] + "= %5.3f" %  best_xform_results[j,1] # transform value error line
        output_file_xform_err_list.append(line)
        line = coef_being_optimized[j] + "= %5.3f" %  999 # transform value r squared line - set to 999 to inidcate no good value
        output_file_xform_r2_list.append(line)
    msg = export_transforms_1(transformtest)
    line = "\n" + msg + "\n"
    status_box.insert("end",line)
    status_box.see("end")
    save_opt_btn.configure(state = "disabled")
        
    return

# Create optimized transform values
    
def optimize_transforms():
    global coef_anal,test_xforms_float,test_xforms_str,final_transforms_to_do,test_xforms_err_float,color_transforms_to_do,status_box,teit_filters,transforms_to_do,test_xforms_str
    global detailed_print_setting,save_opt_btn, best_xform_results, coef_being_optimized,transformtest
#
#  detailed_print_setting =  "N" = don't print, "Y" = print  - controls detailed print in test transforms of every star/transform results  
#    
#
    save_xforms = np.zeros(len(allxforms))  # for possible restore at end
    for i in range(len(allxforms)):
        save_xforms[i] = test_xforms_float[i]
#
#   Check that transforms available - if not, remove from planned calculations
    final_transforms_to_do = []
    final_transforms_bands = []  # track finals xforms to be done based on both images loaded and transforms provided
    flen = len(teit_filters)
    for k in range(len(transforms_to_do)):
        if test_xforms_str[allxforms.index(transforms_to_do[k])] != "NA": 
            final_transforms_to_do.append(transforms_to_do[k]) # add
            if transforms_to_do[k][1:2] not in final_transforms_bands :
                final_transforms_bands.append(transforms_to_do[k][1:2]) # add to list
            if transforms_to_do[k][3:4] not in final_transforms_bands :
                final_transforms_bands.append(transforms_to_do[k][3:4])
            if transforms_to_do[k][4:5] not in final_transforms_bands :
                final_transforms_bands.append(transforms_to_do[k][4:5])
        else:
            status_box.insert("end","No transforms for " + transforms_to_do[k] + "\n")
            status_box.see("end")
    color_transforms_to_do = []
    for i in range(len(final_transforms_to_do)):
        colorxform = "T" + final_transforms_to_do[i][3:5]
        if colorxform not in color_transforms_to_do :
            color_transforms_to_do.append(colorxform)
    coef_being_optimized = final_transforms_to_do + color_transforms_to_do  #  currently not optimizing color - to be added later
    best_xform_results = np.zeros((len(coef_being_optimized),2)) #       will hold best values for each transform after optimization      
    avg_coef_error = np.zeros(len(coef_being_optimized))  # used when optimizing
    num_steps = 50 # number of steps in transform values for optimization
    test_various_xform_values = np.zeros((num_steps,(len(allxforms)))) # set up array of various transform values
    coef_anal_comparison = np.zeros((num_steps,len(coef_being_optimized),8)) # coef_anal_comparison[k,l,m] = collection of data k=test set numer, l,m = coef analysis array items (as listed in coef_anal)
    sigma_factor = 15 # range of transform values will be +/- transform err * sigma_factor
#
#  Progress bar
#
    pbar = ttk.Progressbar(transformtest,orient='horizontal',length=300,mode='determinate')
    pbar.grid(row=20, column = 0,padx=2,pady=2,sticky="NESW")
    for i in range(num_steps) : # for each set
        for j in range(len(final_transforms_to_do)) :
            test_various_xform_values[i,j] = test_xforms_float[allxforms.index(final_transforms_to_do[j])] + 2*sigma_factor/num_steps*(i-int(num_steps/2))*test_xforms_err_float[allxforms.index(final_transforms_to_do[j])]  # Range of values to test -save copy for set i=transform set,j=transform index in
        for k in range(len(color_transforms_to_do)) :
#            print("k, color_transforms_to_do, test_xforms_float[allxforms.index(color_transforms_to_do[k])] =", k, color_transforms_to_do, test_xforms_float[allxforms.index(color_transforms_to_do[k])] )
            test_various_xform_values[i,k + len(final_transforms_to_do)] = test_xforms_float[allxforms.index(color_transforms_to_do[k])]
#  Test magnitude coefficients holding color at initial value
#    
# for each magnitude transform_to_do vary values and analyze
    for i in range(num_steps):  # analyze each set
        pbar.step(2)
        root.update()
        time.sleep(0.1)
        for j in range(len(final_transforms_to_do)):
            test_xforms_float[allxforms.index(final_transforms_to_do[j])] = test_various_xform_values[i,j]
        for k in range(len(color_transforms_to_do)):
            test_xforms_float[allxforms.index(color_transforms_to_do[k])] = test_various_xform_values[i,k + len(final_transforms_to_do)]
        status_box.insert("end","\n ------------------------ Optimization Run %sss -----------------------\n" % i)
        analyze_transforms()
#  Collect Transform Coefficient Analysis Data
#            
#
# coef_anal = array [coefficient index in coeff_being_optimized, analysis data] 
#              list of analysis data items - (0) number of stars (1) average abs error from reference w/o transform (2) average abs error from reference with transform,
#                                            (3) std dev error w/o transform, (4) std dev error with transform, (5) # stars improved, (6) # stars same, (7) # stars worse
#
#  save analysis array from each tranform set and keep best magnitude transform value  
#
        for k in range(len(coef_being_optimized)) :
            xformname = coef_being_optimized[k]
            for m in range(8):
                coef_anal_comparison[i,k,m] = coef_anal[k,m]
            if i == 0:
                best_xform_results[k,0] = test_various_xform_values[i,k]  # set starting value
                avg_coef_error[k] = coef_anal[k,2]
                best_xform_results[k,1] = test_xforms_err_float[allxforms.index(xformname)] # assume original sigma for this transform valud for optimied value
            else:
                if coef_anal[k,2] < avg_coef_error[k]:
                    best_xform_results[k,0] = test_various_xform_values[i,k] # save new coefficient value with minimum error
                    avg_coef_error[k] = coef_anal[k,2] # save new minimum value
    print("New minimum detection - best_xform_results ", best_xform_results)
#               
# optimize color transforms using best magnitude transforms
#       
    for i in range(num_steps) : # for each set
        for j in range(len(final_transforms_to_do)) :
            test_various_xform_values[i,j] = best_xform_results[j,0] # load optimized mag transform value
           
#            test_various_xform_values[i,j] = test_xforms_float[allxforms.index(final_transforms_to_do[j])] + 2*sigma_factor/num_steps*(i-int(num_steps/2))*test_xforms_err_float[allxforms.index(final_transforms_to_do[j])]  # Range of values to test -save copy for set i=transform set,j=transform index in
        for k in range(len(color_transforms_to_do)) :
#            print("k, color_transforms_to_do, test_xforms_float[allxforms.index(color_transforms_to_do[k])] =", k, color_transforms_to_do, test_xforms_float[allxforms.index(color_transforms_to_do[k])] )
            test_various_xform_values[i,k + len(final_transforms_to_do)] = test_xforms_float[allxforms.index(color_transforms_to_do[k])] + 2*sigma_factor/num_steps*(i-int(num_steps/2))*test_xforms_err_float[allxforms.index(color_transforms_to_do[k])]  

    for i in range(num_steps):  # analyze each set
        pbar.step(2)
        root.update()
        time.sleep(0.1)
        for j in range(len(final_transforms_to_do)):
            test_xforms_float[allxforms.index(final_transforms_to_do[j])] = test_various_xform_values[i,j]
        for k in range(len(color_transforms_to_do)):
            test_xforms_float[allxforms.index(color_transforms_to_do[k])] = test_various_xform_values[i,k + len(final_transforms_to_do)]
        status_box.insert("end","\n ------------------------ Optimization Run %sss -----------------------\n" % i)
        analyze_transforms()
#  Collect Transform Coefficient Analysis Data
#            
#
# coef_anal = array [coefficient index in coeff_being_optimized, analysis data] 
#              list of analysis data items - (0) number of stars (1) average abs error from reference w/o transform (2) average abs error from reference with transform,
#                                            (3) std dev error w/o transform, (4) std dev error with transform, (5) # stars improved, (6) # stars same, (7) # stars worse
#
#  save analysis array from each tranform set and keep best magnitude transform value  
#
        for k in range(len(final_transforms_to_do),len(coef_being_optimized)) :
            xformname = coef_being_optimized[k]
            for m in range(8):
                coef_anal_comparison[i,k,m] = coef_anal[k,m]
            if i == 0:
                best_xform_results[k,0] = test_various_xform_values[i,k]  # set starting value
                avg_coef_error[k] = coef_anal[k,2]
                best_xform_results[k,1] = test_xforms_err_float[allxforms.index(xformname)] # assume original sigma for this transform valud for optimied value
            else:
                if coef_anal[k,2] < avg_coef_error[k]:
                    best_xform_results[k,0] = test_various_xform_values[i,k] # save new coefficient value with minimum error
                    avg_coef_error[k] = coef_anal[k,2] # save new minimum value
    print("New minimum detection - best_xform_results ", best_xform_results)
    
# progress bar removal
    pbar.destroy()
    
    
    table = "" # start collection of print information for summary table
    for j in range(len(coef_being_optimized)): # print row section for each transform value, rows for each test set
        xformname = coef_being_optimized[j]

        if detailed_print_setting.get() == "Y":
            line = "\n" + 60*"-" + "\n\nDetailed Optimization Print for " + xformname + "\n\nTest Transform Value\t\tMag Est Err\t\tMag Est Err\n\t\t no xform\t\tw test transform\n "
            print(line)
#            status_box.insert("end",line)
        
        for k in range(num_steps):  # print row for each test set - xform value, average error no transform, average error with transform
            if detailed_print_setting.get() == "Y":
                print("\n%7.3f\t\t%7.3f\t%7.3f" % (test_various_xform_values[k,coef_being_optimized.index(xformname)],coef_anal_comparison[k,j,1], coef_anal_comparison[k,j,2]))
#                status_box.insert("end","\n%7.3f\t\t%7.3f\t%7.3f" % (test_various_xform_values[k,coef_being_optimized.index(xformname)],coef_anal_comparison[k,j,1], coef_anal_comparison[k,j,2]))
            if k == 0:
                best_xform_results[j,0] = test_various_xform_values[k,j]
                avg_error = coef_anal_comparison[k,j,2]
                best_xform_results[k,1] = test_xforms_err_float[allxforms.index(xformname)] # assume original sigma for this transform valud for optimied value
            else:
                if coef_anal_comparison[k,j,2] < avg_error:
                    best_xform_results[j,0] = test_various_xform_values[k,j]
                    avg_error = coef_anal_comparison[k,j,2]
                    best_xform_results[j,1] = test_xforms_err_float[allxforms.index(xformname)] # assume original sigma for this transform valud for optimied value
                    
        table = table + "\n%5s\t\t%7.3f\t\t%7.3f\t\t%7.3f\t\t%7.3f" % (xformname, best_xform_results[j,0],avg_error,save_xforms[allxforms.index(xformname)],coef_anal_comparison[int(num_steps/2),j,2])
#
#    Fix mag transforms at best and vary color transforms to optimize
#
    
    
    
    
    
    
    status_box.insert("end","\n\n                      Optimized Transform Set - Comparison to Original\n\n")
    status_box.insert("end","\n\t\tOpt xform  \t\txform mag err\t\tOrig xform\t\txform mag err")
    status_box.insert("end","\n\t\t Value\t\t\w opt xform\t\tValue\t\tw orig xform")
    status_box.insert("end",table)
    status_box.insert("end","\n")
    status_box.insert("end","\n" + 40*"*" + "\n")
    status_box.see("end")
    for i in range(len(allxforms)):  # Restore orginal transforms
        test_xforms_float[i] = save_xforms[i]
    save_opt_btn.configure(state = "active", activebackground = "#E0FFFF",bg="#E0FFFF")
    return

        
    
        
            


############################################################################################################
#
#                   Perform Analysis of Transform Set on Loaded Image
#
############################################################################################################
def analyze_transforms():
    global allxforms,test_xforms_float,test_xforms_str, test_xforms_err_float, test_xforms_err_str,img_set_filters
    global status_box,img_set_filters,coef_anal,final_transforms_to_do,detailed_print_setting,coef_anal,color_transforms_to_do
    global max_num_test_stars,teit,teit_test_star_auid,save_opt_btn,comp_star_setting,auid_comp_star,plot_data
    
#
#  detailed_print_setting =  "N" = don't print, "Y" = print  - controls detailed print in test transforms of every star/transform results  
#    
    
#      
##
##   CALCULATE TRANSORMED MAGNITUDES
#  teit format - because of VPHOT erratic star id numbering use B-V to identify standard stars - and allow for later
#       addition of TEIT_AUID list of  AUID's matching each row in TEIT
##
#       first index star id (matches teit_test_star_auid list - i.e.  teit[m,] has AUID of teit_test_star_auid[m])
#       Second number :
#       Column 0 -  B-V of reference star
#       Column 1-(2*cur_filt) - standard star reference mag and error - format U, Uerr, B, Berr, etc.
#       Column 2*num_filt +1 -> 2*num_filt + 3*cur_filt - machine mag, err, airmass - formt u,uerr,uairmass,b,berr,bairmass etc.
#
#   Check that transforms available - if not, remove from planned calculations
    line = "\n" + + 10*"&" + "     START OF SINGLE TEST OF TRANSFORMATION COEFFICIENTS     " + 20*"&" + "\n"
    status_box.insert("end",line)
    
    save_opt_btn.configure(state="disabled") # disable save button for previous optimized transforms since new set being evaluated/created
    final_transforms_to_do = []
    final_transforms_bands = []  # track finals xforms to be done based on both images loaded and transforms provided
    flen = len(teit_filters)
    for k in range(len(transforms_to_do)):
        if test_xforms_str[allxforms.index(transforms_to_do[k])] != "NA": 
            final_transforms_to_do.append(transforms_to_do[k]) # add
            if transforms_to_do[k][1:2] not in final_transforms_bands :
                final_transforms_bands.append(transforms_to_do[k][1:2]) # add to list
            if transforms_to_do[k][3:4] not in final_transforms_bands :
                final_transforms_bands.append(transforms_to_do[k][3:4])
            if transforms_to_do[k][4:5] not in final_transforms_bands :
                final_transforms_bands.append(transforms_to_do[k][4:5])
        else:
            status_box.insert("end","No transforms for " + transforms_to_do[k] + "\n")
            status_box.see("end")

#
#   Select Comp Star
#
    comp_star_ref_mags = np.zeros((len(teit_filters),2)) # slots for mag, mag erors
    comp_star_inst_mags = np.zeros((len(teit_filters),2))
#
#
#  Set up array to save data for plotting of transforms vs actual star data
#          plot_data[x,y,z] where x is star number, y is transform identifier , z (0) is untransformed mag minus ref, z(1) is color difference of target minus comp, z(2) = untransformed mag error
#                z(3) is transformed mag minus ref, z(4) is transformed mag estimate error
    plot_data = np.zeros((max_num_test_stars,len(final_transforms_to_do),5))
#
#  Get comp star option setting and set up as requested
#
#
    if comp_star_setting.get() == "MinError" :  # Minimum abs error across all bands selected
        lowest_error = 100  # set up to count lowest error mag across all filters of images loaded
        for i in range(max_num_test_stars):
            num_filt_w_data = 0
            avg_error = 0
            for j in range(flen): #range(5) : # all filters
                if teit[i,2*j+2] == 0 : # go to next star if star doesn't have alues for all filters
                    break
                num_filt_w_data += 1
                avg_error = ((num_filt_w_data - 1)*avg_error + teit[i,2*j + 2])/num_filt_w_data
            if avg_error < lowest_error and avg_error != 0 :  # ignore star with bad data
                lowest_error = avg_error
                comp_star_id = teit_test_star_auid[i]
                for j in range(5):
                    comp_star_ref_mags[j,0] = teit[i,2*j +1] # comp ref mag
                    comp_star_ref_mags[j,1] = teit[i,2*j +2] # comp ref error
                    comp_star_inst_mags[j,0] = teit[i,2*flen + 3*j + 1] # comp instrument mag
                    comp_star_inst_mags[j,1] = teit[i,2*flen + 3*j + 2] # comp instrument mag error
                    
    elif comp_star_setting.get() == "Ensemble" : # Ensemble selected
        test_star_count = np.zeros(flen)
        comp_star_id = "Ensemble of all Reference Stars"
        for i in range(max_num_test_stars):
            for j in range(flen):
                if teit[i,2*flen + 3*j + 1] == 0 :  # test if instrument magnitude available - if not, skip this band
                    continue
                else:
                    comp_star_ref_mags[j,0] += teit[i,2*j + 1] # add current ref mag to total
                    comp_star_inst_mags[j,0] += teit[i,2*flen + 3*j + 1] # add current instrument mag to totak
                    comp_star_ref_mags[j,1] += teit[i,2*j + 2]**2 # add square of error for ref mag
                    comp_star_inst_mags[j,1] += teit[i,2*flen + 3*j + 2]**2 # add square of error for instrument mags
                    test_star_count[j] += 1  # add 1 to star count for this filter
        for j in range(flen):  
            comp_star_ref_mags[j,0] = comp_star_ref_mags[j,0] / test_star_count[j]
            comp_star_ref_mags[j,1] = math.sqrt(comp_star_ref_mags[j,1] / test_star_count[j])
            if comp_star_inst_mags[j,0] != 0 : # be sure measurements were taken
                comp_star_inst_mags[j,1] = math.sqrt(comp_star_inst_mags[j,1] / test_star_count[j])
                comp_star_inst_mags[j,0] = comp_star_inst_mags[j,0] / test_star_count[j] # error

    else:  # must be auid input
        comp_star_id = auid_comp_star.get().strip() # remove any spaces in comp star auid
        for i in range(len(teit_test_star_auid)) :
            if comp_star_id == teit_test_star_auid[i]:
                break
            if i != len(teit_test_star_auid) - 1:
                continue
            else:
                Errormsg("Comp Star " + comp_star_id + " not in field")
                return
        for j in range(flen):
            comp_star_ref_mags[j,0] = teit[i,2*j + 1]
            comp_star_inst_mags[j,0] = teit[i, 2*flen + 3*j + 1]
            comp_star_ref_mags[j,1] = teit[i, 2*j + 2]
            comp_star_inst_mags[j,1] = teit[i, 2*flen + 3*j + 2]
        
            
            


#
#
#  Butild Transformation Matrix
#
#    
##
##  xform_matrix - for each star (index 1) and transform done (index 2) - third index = (0)ref mag, (1)ref error, (2)untransformed mag, (3)untransformed mag error,
##                  (4)untransformed mag minus ref mag, (5)transformed mag, (6)transformed mag error, (7)transformed mag minus ref mag
##    c
    if detailed_print_setting.get() == "Y":  # print validation test data
        print(" " + 50*"*" + "\n" + 50*"*" + "\n")
        print("                    TRANSFORMATION VALIDATION TESTING DATA")
        print("\n\nComp Star AUID - ",comp_star_id)
        print("\n   U\t   B\t   V\t   R\t   I\t\t   u\t   b\t   v\t   r\t   i")
        print("%7.3f\t%7.3f\t%7.3f\t%7.3f\t%7.3f\t\t%7.3f\t%7.3f\t%7.3f\t%7.3f\t%7.3f" % (comp_star_ref_mags[0,0],comp_star_ref_mags[1,0],comp_star_ref_mags[2,0],
                comp_star_ref_mags[3,0],comp_star_ref_mags[4,0],comp_star_inst_mags[0,0],comp_star_inst_mags[1,0],comp_star_inst_mags[2,0],
                comp_star_inst_mags[3,0],comp_star_inst_mags[4,0]))
#    print("\n\ncomp_star_ref_mags,comp_star_inst_mags = ",comp_star_ref_mags,comp_star_inst_mags)
    xform_matrix = np.zeros((max_num_test_stars,len(final_transforms_to_do),8))
    if detailed_print_setting.get() == "Y" :
        status_box.insert("end","\n\n***************************** ANALYSIS RESULTS  *********************************************************************************")
        table_columns = "\n\nStar AUID\t        B-V\t     Band\tColor\tRefMag\tno xform\tno xf err\txform adj\t xform\t xf err\tImprov (+yes/-no)\n"
        status_box.insert("end",table_columns)
        status_box.see("end")
    final_test_star_auids = []
    display_lines = 0
#
#  Determin what color transfors to analyze
#
    color_transforms_to_do = []
#    print("final_transforms_to_do = ",final_transforms_to_do)
    for i in range(len(final_transforms_to_do)):
        colorxform = "T" + final_transforms_to_do[i][3:5]
        if colorxform not in color_transforms_to_do :
            color_transforms_to_do.append(colorxform)
    coef_anal = np.zeros((len(final_transforms_to_do) + len(color_transforms_to_do) ,8)) # coefficient analysis array - defined below
##
#
#    Start transformation of every star
#
#
    if detailed_print_setting.get() == "Y":
        print("\n Transformation Coefficients")
        for m in range(len(allxforms)):
            print("%s\t%7.3f" % (allxforms[m],test_xforms_float[m]))
    for i in range(max_num_test_stars):  # star id in teit_star_auid[i]
        for j in range(len(final_transforms_to_do)): # transform_name in transforms_to_do[j]
            band = final_transforms_to_do[j][1:2]  # will be u,b,v,r,i
            band_index = teit_filters.index(band.upper())
            color1 = final_transforms_to_do[j][3:4]
            color1_index = teit_filters.index(color1.upper())
            color2 = final_transforms_to_do[j][4:5]
            color2_index = teit_filters.index(color2.upper())
            color = color1 + color2
            band_upper = band.upper()
# Store target star reference mag and reference mag error
            xform_matrix[i,j,0] = teit[i,2*teit_filters.index(band_upper) + 1 ] # star i band j reference mag
            xform_matrix[i,j,1] = teit[i,2*teit_filters.index(band_upper) + 2 ] # star i band j reference mag error
#  teit format - because of VPHOT erratic star id numbering use B-V to identify standard stars - and allow for later
#       addition of TEIT_AUID list of  AUID's matching each row in TEIT
##
#       first index star id (matches star_id_list)
#       Second number :
#       Column 0 -  B-V of reference star
#       Column 1-(2*cur_filt) - standard star reference mag and error - format U, Uerr, B, Berr, etc.
#       Column 2*num_filt +1 -> 2*num_filt + 3*cur_filt - machine mag, err, airmass - formt u,uerr,uairmass,b,berr,bairmass etc.
#
# check for missing data - skip star for this transform
#
            if ( teit[i,2*flen + 3*color1_index + 1] == 0 or teit[i,2*flen + 3*color2_index + 1] == 0
                or teit[i,2*flen + 3*band_index + 1] == 0  or comp_star_inst_mags[color1_index,0] == 0 or comp_star_inst_mags[color2_index,0] == 0 ) :
                continue  # not all measurements available
#                
#  Limit stars to B-V > .5
#
#            if abs(teit[i,3] - teit[i,5]) < 0.5 :
#                continue
                
            untransformed_mag_estimate = comp_star_ref_mags[band_index,0] + teit[i,2*flen + 3*band_index + 1] - comp_star_inst_mags[band_index,0] # untransformed mag estimate
            untransformed_mag_error = untransformed_mag_estimate - xform_matrix[i,j,0]
            if abs(untransformed_mag_error) > .5 :  # appears to be bad star measurement - do not use
                continue
            if detailed_print_setting.get() == "Y" :
                if display_lines == 32:
                    status_box.insert("end",table_columns)
                    display_lines = 0
                display_lines += 1
            if teit_test_star_auid[i] not in final_test_star_auids:
                final_test_star_auids.append(teit_test_star_auid[i])
            xform_matrix[i,j,2] = untransformed_mag_estimate # untransformed mag estimate] 
            xform_matrix[i,j,3] = math.sqrt(comp_star_inst_mags[band_index,1]**2 + comp_star_ref_mags[band_index,1]**2 + teit[i,2*flen + 3*band_index + 2]**2)  # untransformed mag est err
            xform_matrix[i,j,4] = untransformed_mag_error # untransformed minus ref = untransformed error
            color_transform_name = "T" + color1 + color2
#            print("\nteit[i,2*flen + 3*color1_index + 1],teit[i,2*flen + 3*color2_index + 1],comp_star_inst_mags[color1_index,0],comp_star_inst_mags[color2_index,0]",teit[i,2*flen + 3*color1_index + 1],teit[i,2*flen + 3*color2_index + 1],comp_star_inst_mags[color1_index,0],comp_star_inst_mags[color2_index,0])
            delta = test_xforms_float[allxforms.index(color_transform_name)]*(
                    (teit[i,2*flen + 3*color1_index + 1] - teit[i,2*flen + 3*color2_index + 1]) 
                    - (comp_star_inst_mags[color1_index,0] - comp_star_inst_mags[color2_index,0]))
            delta_err1 = test_xforms_err_float[allxforms.index(color_transform_name)]*math.sqrt(teit[i,2*flen + 3*color1_index + 1]**2 + teit[i,2*flen + 3*color2_index + 1]**2 + (
                    (comp_star_inst_mags[color1_index,0]**2 + comp_star_inst_mags[color2_index,0]**2))) 
            delta_err2 = test_xforms_float[allxforms.index(color_transform_name)]*(math.sqrt(teit[i,2*flen + 3*color1_index + 2]**2 + teit[i,2*flen + 3*color2_index + 2]**2 + (
                    (comp_star_inst_mags[color1_index,1]**2 + comp_star_inst_mags[color2_index,1]**2))))
            delta_err3 = test_xforms_err_float[allxforms.index(color_transform_name)]*(math.sqrt(teit[i,2*flen + 3*color1_index + 2]**2 + teit[i,2*flen + 3*color2_index + 2]**2 + (
                    (comp_star_inst_mags[color1_index,1]**2 + comp_star_inst_mags[color2_index,1]**2))))
            delta_err = math.sqrt(delta_err1**2 + delta_err2**2 + delta_err3**2)
#            print("\ntest_xforms_float[allxforms.index(color_transform_name)],delta = ",test_xforms_float[allxforms.index(color_transform_name)],delta)
#
#   collect data for plotting transforms vs actual measurments
#
            plot_data[i,j,0] = untransformed_mag_error  # difference between untransformed mag and reference mag
            plot_data[i,j,2] = xform_matrix[i,j,3] # untransformed_mag_error measurement error 
            plot_data[i,j,1] = (teit[i,2*flen + 3*color1_index + 1] - teit[i,2*flen + 3*color2_index + 1]) - (
                    comp_star_inst_mags[color1_index,0] - comp_star_inst_mags[color2_index,0])  # delta color difference target minus comp

#
#
            xformamount = test_xforms_float[allxforms.index(final_transforms_to_do[j])] * delta
            xform_matrix[i,j,5] = xform_matrix[i,j,2] + xformamount # transformed magnitude
            xform_matrix[i,j,6] = math.sqrt(untransformed_mag_error**2 + delta_err**2)
            xform_matrix[i,j,7] = xform_matrix[i,j,5] - xform_matrix[i,j,0] # transformed minus ref = transformed error
            xform_improvement = abs(xform_matrix[i,j,4]) - abs(xform_matrix[i,j,7]) # positive is improvement, negative worse
            ref_B_minus_V = teit[i,3] - teit[i,5] # ref mag B - V
            
            plot_data[i,j,3] = xform_matrix[i,j,7] # transformed mag minus reference mag
            plot_data[i,j,4] = math.sqrt(xform_matrix[i,j,6]**2 + comp_star_ref_mags[band_index,1]**2) # transformed mag minus reference mag error
            
            
            text = "\n%11s\t%8.3f\t%2s\t%2s\t%8.3f\t%8.3f\t%8.3f\t%8.3f\t%8.3f\t%8.3f\t%6.3f" %(teit_test_star_auid[i],ref_B_minus_V,band,color,xform_matrix[i,j,0],xform_matrix[i,j,2],
                                                                                  xform_matrix[i,j,4],xformamount,xform_matrix[i,j,5],xform_matrix[i,j,7],xform_improvement)
            if detailed_print_setting.get() == "Y":
                status_box.insert("end",text)
#  Collect Transform Coefficient Analysis Data
#            
#
# coef_anal = array [coefficient index in final transforms_to_do + color_transforms_to_do, analysis data] 
#              list of analysis data items - (0) number of stars (1) average abs error from reference w/o transform (2) average abs error from reference with transform,
#                                            (3) std dev error w/o transform, (4) std dev error with transform, (5) # stars improved, (6) # stars same, (7) # stars worse
#
#      Add data to both color transform and magnitude transform data
            list = [j,len(final_transforms_to_do) + color_transforms_to_do.index("T" + color)]
            for k in list :
                an = coef_anal[k,0] # number of previous stars for use in computing accumulating average
                coef_anal[k,0] = coef_anal[k,0] + 1 # number of stars measured with this transform coefficient (final_transforms_to_do[j])
                coef_anal[k,1] = (coef_anal[k,1]*an + abs(xform_matrix[i,j,4]))/(an + 1) # average abs(error) without transform
                coef_anal[k,2] = (coef_anal[k,2]*an + abs(xform_matrix[i,j,7]))/(an + 1) # average abs(error) with transform
                coef_anal[k,3] = np.sqrt((an*(coef_anal[k,3])**2 + xform_matrix[i,j,4]**2)/(an + 1)) # std dev error w/o transforms
                coef_anal[k,4] = np.sqrt((an*(coef_anal[k,4])**2 + xform_matrix[i,j,7]**2)/(an + 1)) # std dev error with transforms
#
#  Limit counting to larger corrections
#
#                if abs(xform_matrix[i,j,4] - xform_matrix[i,j,7]) > 0.02:  # line added to count larger corrections only
                if abs(xform_matrix[i,j,4] - xform_matrix[i,j,7]) < 0.01 : # tolerance to inlcude star in count of minimal change < .01
                    coef_anal[k,6] += 1 # count as minimal change
                elif abs(xform_matrix[i,j,4]) > abs(xform_matrix[i,j,7]) : # transform improved accuracy
                    coef_anal[k,5] += 1
                else:
                    coef_anal[k,7] += 1 # error worse
        if detailed_print_setting.get() == "Y":
            stepsize = int(max_num_test_stars/10.) + 1 
            if float(i/stepsize) == int(i/stepsize) :  # randomly pick 10 of stars to test
                print("\n" + 75*"-" + "\nTest Star AUID = ",teit_test_star_auid[i])
                print("\n   B-V\t   U\t   B\t   V\t   R\t   I\n%7.3f\t%7.3f\t%7.3f\t%7.3f\t%7.3f\t%7.3f" % (teit[i,0],teit[i,1],teit[i,3],teit[i,5],teit[i,7],teit[i,9]))
                print("\n\n\t   u\t   b\t   v\t   r\t   i\n\t%7.3f\t%7.3f\t%7.3f\t%7.3f\t%7.3f" % (teit[i,11],teit[i,14],teit[i,17],teit[i,20],teit[i,23]))
                print(("\n" + 5*("\tairmass") + "\n\t" + 5*("%8.3f")) % (teit[i,13],teit[i,16],teit[i,19],teit[i,22],teit[i,25]))
                print("\nResults:\n\nTransform\tFilter\t   Ref\t\t   Not\t\t xformed\n\t\t\t   Mag\t\t xformed\n")
                for mn in range(len(final_transforms_to_do)):
                    filter = final_transforms_to_do[mn][1:2].upper()
                    print("\n %s\t\t%s\t%8.3f\t%8.3f\t%8.3f" % (final_transforms_to_do[mn],filter,xform_matrix[i,mn,0],xform_matrix[i,mn,2],xform_matrix[i,mn,5]))


    status_box.insert("end","\n\nComp Star Used for test field - " + comp_star_id )
    status_box.insert("end","\nBand\tRef Mag\tErr")
    for i in range(5):
        if teit_filters[i].lower() in final_transforms_bands:
            status_box.insert("end","\n  " + teit_filters[i] + "\t %05.3f \t %05.3f" % (comp_star_ref_mags[i,0], comp_star_ref_mags[i,1]))
    status_box.insert("end","\n")
    status_box.see("end")

    status_box.insert("end","\n\n*******      Coefficient Analysis  ***********")
    status_box.insert("end","\nCoef\tCoef\t# star\tavg err\tavg err\tstd dev\tstd dev\t#improv\t# within\t#worse\n")
    status_box.insert("end","\tvalue\ttests\tno xform\tw/xform\tno xform\tw/xform\t\t  .01")
    for i in range(len(final_transforms_to_do) + len(color_transforms_to_do)) :
        if i < len(final_transforms_to_do) :
            xformname = final_transforms_to_do[i]
        else:
            xformname = color_transforms_to_do[i-len(final_transforms_to_do)]
        coef_value = test_xforms_float[allxforms.index(xformname)]
        format = "\n%5s\t%7.3f\t%5d\t%8.3f\t%8.3f\t%8.3f\t%8.3f\t%d\t%d\t%d"
        status_box.insert("end",format % (xformname,coef_value,coef_anal[i,0],coef_anal[i,1],coef_anal[i,2],coef_anal[i,3],coef_anal[i,4],coef_anal[i,5],coef_anal[i,6],coef_anal[i,7]))
    status_box.see("end")
    line = "\n\n" + 10*"&"  + "     END OF SINGLE TEST OF TRANSFORMATION COEFFICIENTS     " + 20*"&" + "\n"
    status_box.insert("end",line)
#  INDENT STOP FOR COMP STAR TEST




    return comp_star_id
#
#  END OF TRANSFORM ANALYSIS
#
#
############################################################################################################    
# function to load TA Format ini file of transform values
############################################################################################################

def loadini():
    global allxforms,test_xforms_float,test_xforms_str, test_xforms_err_float, test_xforms_err_str,translabel
    global status_box,transformtest,perf_anal_btn,plot_xform_anal_btn, create_opt_btn, save_opt_btn, xforms_and_images_loaded
# initialize
    test_xforms_str = [] # intialize 
    test_xforms_err_str = [] #initialize
    for i in range(len(allxforms)) :
        test_xforms_str.append("NA")
        test_xforms_err_str.append("NA")
    test_xforms_err_float = np.zeros(len(allxforms)) # initialize float of errors
    test_xforms_float = np.zeros(len(allxforms)) # initialize float of values
    inifilename = askopenfilename(title = "Select File in TA ini format of Transformation Coefficients to be tested",parent=transformtest)
    xformini = open(inifilename,"r") # open file for reading
    coef_start = "N"  # keep as No until [Coefficients] line found
    error_start = "N" # keep as No until [Error] line found
    for i in range(len(allxforms)) :
        test_xforms_str[i] = "NA"
        test_xforms_err_str[i] = "NA"
    for line in xformini :
        delim = ["=","="]
        aline = []
        lineparse(line,aline,delim)
        if coef_start == "N" and error_start == "N" : # before finding coef line
            if aline[0] != "[Coefficients]" : # look for coefficients line
                continue # go to next line
            else: # found coef line
                coef_start = "Y"
                continue # read next line
        if coef_start == "Y" and error_start == "N" : # reading coef lines
            if aline[0] == "[Error]" :  # Found start of error estimates
                error_start = "Y"
                continue # to to next line
            k = allxforms.index(aline[0])
            test_xforms_str[k] = aline[1] # save transform string
            test_xforms_float[k] = float(aline[1])
        if coef_start == "Y" and error_start == "Y": # reading transform error lines
            if aline[0] == "[R Squared Values]" : # all transforms and errors have been saved
                break # don't read any more lines
            k = allxforms.index(aline[0])
            test_xforms_err_str[k] = aline[1]
            test_xforms_err_float[k] = float(aline[1])
#    for i in range(len(allxforms)) :
#        print("i,test_xforms_str, test_xforms_float, test_xforms_err_str, test_xforms_err_float = ", i,test_xforms_str[i], test_xforms_float[i], test_xforms_err_str[i], test_xforms_err_float[i])
    text = "\nTransforms Loaded (transform value, error)"
    status_box.insert("end",text + "\n")
    num_coef = 0
    text = ""
    for k in range(len(allxforms)):
        if test_xforms_str[k] == "NA" :
            continue  # if no value, skip
        num_coef += 1
        a = '{:>1s}'.format(allxforms[k])
        b = '{:05.3f}'.format(test_xforms_float[k])
        c = '{:05.3f}'.format(test_xforms_err_float[k])
        text = a + "\t" + b + "\t" + c
        status_box.insert("end",text + "\n")
    status_box.see("end")
# xforms_and_images_loaded = "N" # set up indicator if anlysis data loaded - N=none,I=images,T=Transforms,TI = images and transforms
    print("xfi]orms_and_images_loaded = ",xforms_and_images_loaded)

    if xforms_and_images_loaded == "N":
        xforms_and_images_loaded = "T"
    elif xforms_and_images_loaded == "I":
        xforms_and_images_loaded = "TI"
        perf_anal_btn.configure(state="active", bg="#E0FFFF", activebackground = "#E0FFFF")
        plot_xform_anal_btn.configure(state="active", bg="#E0FFFF", activebackground = "#E0FFFF")
        create_opt_btn.configure(state="active", bg="#E0FFFF", activebackground = "#E0FFFF")
        save_opt_btn.configure(state="active", bg="#E0FFFF", activebackground = "#E0FFFF")
    transformtest.lift()
    
            

    return
# function to allow typed entry of transform values
# 
# saved entered transforms for use here
#
def loadtypedtransforms():
    global allxforms, status_box,test_xforms_float,test_xforms_str,test_xforms_err_float,test_xforms_err_str,tflabels,tferrlabels,errwindow,loaderr
    global transformtest,typeintransforms,perf_anal_btn ,plot_xform_anal_btn, create_opt_btn, save_opt_btn,xforms_and_images_loaded
# Load values 
    loaderr = 0
    try:
        for i in range(len(allxforms)):
            test_xforms_str[i] = tflabels[i].get()
            if (test_xforms_str[i] == "") or (test_xforms_str[i] == "None") or (test_xforms_str[i] == "NA") :
                test_xforms_str[i] = "NA"
            else:
                test_xforms_float[i] = float(test_xforms_str[i])
            test_xforms_err_str[i] = tferrlabels[i].get()
            if (test_xforms_err_str[i] == "") or (test_xforms_err_str[i] == "None") or (test_xforms_err_str[i] == "NA"):
                test_xforms_err_str[i] = "NA"
            else:
                test_xforms_err_float[i] = float(test_xforms_err_str[i])
    except:
        Errormsg("Invalid entry - " + allxforms[i])
        loaderr = 1 # indicate input error
        root.wait_window(errwindow)
        return
    text = "\nTransforms Loaded (transform value, error)"
    status_box.insert("end",text + "\n")
    num_coef = 0
    text = ""
    for k in range(len(allxforms)):
        if test_xforms_str[k] == "NA" :
            continue  # if no value, skip
        num_coef += 1
        a = '{:>1s}'.format(allxforms[k])
        b = '{:05.3f}'.format(test_xforms_float[k])
        c = '{:05.3f}'.format(test_xforms_err_float[k])
        text = a + "\t" + b + "\t" + c
        status_box.insert("end",text + "\n")
    status_box.see("end")
# xforms_and_images_loaded = "N" # set up indicator if anlysis data loaded - N=none,I=images,T=Transforms,TI = images and transforms
    if xforms_and_images_loaded == "N":
        xforms_and_images_loaded = "T"
    elif xforms_and_images_loaded == "I":
        xforms_and_images_loaded = "TI"
        perf_anal_btn.configure(state="active", bg="#E0FFFF")
        plot_xform_anal_btn.configure(state="active",bg="#E0FFFF")
        create_opt_btn.configure(state="active", bg="#E0FFFF")
        save_opt_btn.configure(state="active",bg="#E0FFFF")    
    transformtest.lift()
    typeintransforms.destroy()
    return

# load transforms from menu for analysis AND create TA ini file of these values
def loadsave_typedtransforms():
    global allxforms, status_box,test_xforms_str,test_xforms_err_str,loaderr
    loadtypedtransforms() # Load typed in values into array
    if loaderr == 1:
        return  # let user fix error
# save transforms to file
    export_file = asksaveasfile(mode="w",defaultextension = ".ini",
                                title = "Enter Name to be used for Saved Transforms File")
    curtime = strftime("%Y_%m_%d_%H:%M:%S",gmtime())
    avg_xforms_record = "[Setup]\ndescription= TG" + version 
    avg_xforms_record = avg_xforms_record + "Time created (UT) = "+ curtime + " Saved When User Either Entered Transforms manually or Saved Optimized Transforms\n"
    avg_xforms_record = avg_xforms_record + "[Coefficients]\n"
    errorlist = ""
    for i in range(len(allxforms)): 
        if test_xforms_str[i] != "NA":
            avg_xforms_record = avg_xforms_record + allxforms[i] + "=" + test_xforms_str[i] + "\n"
            errorlist = errorlist + allxforms[i] + "=" + test_xforms_err_str[i] + "\n"
    avg_xforms_record = avg_xforms_record + "[Error]\n"
    avg_xforms_record = avg_xforms_record + errorlist
    export_file.write(avg_xforms_record)
    export_file.close()
    fname = export_file.name
    status_box.insert("end", "Transforms Saved at UT\n" + curtime + " to TA ini format file\n" + fname + "\n\n")    
    transformtest.lift()

    return


def entertransforms():
    global allxforms, status_box,test_xforms_float,test_xforms_str,test_xforms_err_float,test_xforms_err_str,tflabels,tferrlabels
    global typeintransforms,xform_manual_entry_started

    test_xforms_str = [] # intialize 
    test_xforms_err_str = [] #initialize
    for i in range(len(allxforms)) :
        test_xforms_str.append("NA")
        test_xforms_err_str.append("NA")
    test_xforms_err_float = np.zeros(len(allxforms)) # initialize float of errors


    typeintransforms = Toplevel()
    typeintransforms.title("Enter Transform Values")
    w, h = root.winfo_screenwidth(), root.winfo_screenheight()
    typeintransforms.geometry("%dx%d+0+0" % (.5*w, .8*h))
    Label(typeintransforms,text="Enter Transform Values\n(Leave uncalculated\ntransforms blank)",font=12).grid(row=0,column=1,columnspan=2)
    Label(typeintransforms,text="Transform\nValue",font=12).grid(row=1,column=1,padx=2)
    Label(typeintransforms,text="Transform\nError",font=12).grid(row=1,column=2,padx=2)
# create field entry labels
    tflabels, tferrlabels = [],[]
    for i in range(len(allxforms)):
        tflabels.append("tf_" + allxforms[i])
        tferrlabels.append("tf_err" + allxforms[i])
        Label(typeintransforms,text=allxforms[i],font=12).grid(row=i+2,column=0,pady=2, sticky = "E", padx=1)
        tflabels[i] = Entry(typeintransforms, width = 8,font=12)
        tflabels[i].grid(row=i+2,column=1,pady=2)
        tferrlabels[i] = Entry(typeintransforms, width = 8,font = 12)
        tferrlabels[i].grid(row=i+2,column=2,pady=2)
        if xform_manual_entry_started == 0:
            tflabels[i].delete(0,END)  # clear previous text
            tflabels[i].insert(0,"None")
            xform_manual_entry_started = 0 # set indicator for next use
            tferrlabels[i].delete(0,END)
            tferrlabels[i].insert(0,"None")
        else:  # restore previous values
            tflabels[i].delete(0,END)
            tflabels[i].insert(0,test_xforms_str[i])
            tferrlabels[i].delete(0,END)
            tferrlabels[i].insert(0,test_xforms_err_str[i])
       
    xform_manual_entry_started = 1 # set for next uses during this rus to use saved xforms

    Button(typeintransforms,text="Use for analysis",command=loadtypedtransforms,font=12).grid(row=len(allxforms)+4,column=1,pady=2,columnspan=2)
    btn2 = Button(typeintransforms,text="Use for analysis AND\nSave .ini TA Format file",command=loadsave_typedtransforms,font=12)
    btn2.grid(row=len(allxforms)+5,column=1,pady=2,columnspan=2)
    return

# function to load VPHOT images of transform test field
def vphotload():
    global transformtest,teit,teit_filters,num_filt,status_box, transforms_to_do,num_ref_stars,test_xforms_float
    global star_id_list,star_id_list_label,std_field_mags,std_field_star_count,searchfield,sf_col_list # variables for reference star mag retrieval
    global max_num_test_stars, teit_test_star_auid,img_set_filters,meas_JD,std_field_name,extinction_setting,tel_id,detailed_print_setting
    global perf_anal_btn, plot_xform_anal_btn, create_opt_btn, save_opt_btn, xforms_and_images_loaded
    transformtest.lift()
#
#  Define Major Tables for testing transforms
#
#  teit = Transform Evaluation Input Table - numpy array
    teit_filters = ["U","B","V","R","I"]  # set up to allow easy program additions for other fiters
    num_filt = len(teit_filters)  # number of filters
##
#  teit format - because of VPHOT erratic star id numbering use B-V to identify standard stars - and allow for later
#       addition of TEIT_AUID list of  AUID's matching each row in TEIT
##
#       Column 0 -  B-V of reference star
#       Column 1-(2*cur_filt) - standard star reference mag and error - format U, Uerr, B, Berr, etc.
#       Column 2*num_filt +1 -> 2*num_filt + 3*cur_filt - machine mag, err, airmass - formt u,uerr,uairmass,b,berr,bairmass etc.
#
# 
#   tat = Transform Analysis Table
#
#       Column 0 - B-V of reference star
#       Column 1 - xform identifier (Ta_bc) where a is filter and bc color filters
#       Column 2 - [(0)untransformed mag; (1)untransformed mag error; (2)transformed mag;(3)transformed mag error;
#                  (4)reference minus untransformed mag;(5)reference minus untransformed mag error;
#                  (6)reference minus transformed mag; (7)reference minus transformed mag error]
#
#    Inirialize

    teit = np.zeros((500,5*num_filt + 1)) # allow up to 500 reference stars - maybe change later to count
    fn = askopenfilenames(title = "Select VPHOT files for Transform Coefficient Test",parent=transformtest) # get VPHOT files of Standard Field Observation
    std_field_files = root.tk.splitlist(fn)
    if len(std_field_files) > 5:
        Errormsg("Maximum of 5 files")
        return
#  teit format - because of VPHOT erratic star id numbering use B-V to identify standard stars - and allow for later
#       addition of TEIT_AUID list of  AUID's matching each row in TEIT
##
#       Column 0 -  B-V of reference star
#       Column 1-(2*cur_filt) - standard star reference mag and error - format U, Uerr, B, Berr, etc.
#       Column 2*num_filt +1 -> 2*num_filt + 3*cur_filt - machine mag, err, airmass - formt u,uerr,uairmass,b,berr,bairmass etc.
###### copy insert to be cleaned up
    
    vphot_star_id = []
    for i in range(500):  # nax number of vphot comps allowed is 500 
        vphot_star_id.append(" ")    # create array with vphot id's tied to AUID  (star_id_list)
    vphot_col_list = ["Vphot_Star_id","IM","SNR","X","Y","Sky","Air","B-V","Ref-mag","Target estimate","Active"]
    srow = -1 # initialize index of last row with valid data in teit
    img_set_filters = [] #Set filter used list to empty
    meas_JD = "None"
    obs_date = []
    max_num_test_stars = 0 # track the maximum number of test stars across this set of VPHOT images - will be max searched in teit
    for file_i in range(len(std_field_files)): # process each file listed
        measurements = open(std_field_files[file_i],mode="r")  # retrieve instrument measurements file
        starline_found = "N"
        for oneline in measurements: # process each line in the file
            if oneline == "\n" or oneline == "\r\n":
                continue # read next line
            aline = [] # create holding list for parsed oneline
            delim = ["\t",":"]  # tab delimeter
            lineparse(oneline,aline,delim)
            if starline_found == "N": #process header lines
                if aline[0][:14] == "Primary target":
                    std_field_name = aline[1]
                if aline[0][:7] == "Filter":  # find Filter line.
                    currentfilter = aline[1].lower().strip()
                    img_set_filters.append(currentfilter) # add filter to list of what has been loaded
                    continue
                if aline[0] == "JD":  #Find Julian Date
                    meas_JD = aline[1].strip()
                    continue
                if aline[0] == "Star": # Found line ahead of measurement data - set to process measurement lines
                    starline_found = "Y"
                if aline[0] == "Observation date/time":
                    obs_date.append(aline[1] + ":" + aline[2] + ":" + aline[3] + "-" + currentfilter) # save list of obs times for display and its filter
                if aline[0] == "Primary target" :
                    targetname = aline[1]
                if aline[0] == "R.A." :
                    ra = aline[1] + ":" + aline[2] +":" + aline[3]
                    searchra = str(15*(float(aline[1])+float(aline[2])/60+float(aline[3])/3600))[:8]
                if aline[0] == "Dec." :
                    dec = aline[1] + ":" + aline[2] + ":" + aline[3]
                    searchdec = str((abs(float(aline[1]))+float(aline[2])/60+float(aline[3])/3600))[:6]
                    if "-" in aline[1]:
                        searchdec = "-" + searchdec
                continue  # done looking at header lines - most ignored
#
# Start processing lines of measurement data following "Star" line
#
            else:  # process measurement lines
                floatbv = float(aline[vphot_col_list.index("B-V")])
                if srow == -1 : # Set start row to 0 if first table entry
                    star_row = 0
                    srow = 1 # set number of stars in table to one for first entry
                else:
                    row_found = "N"
                    for j in range(srow): # search current table for B-V match
                        if abs((teit[j,0] - floatbv)) < .001 :
                            star_row = j  # current star row
                            row_found = "Y"
                            break
                    if row_found == "N":
                        star_row = srow  # add index to new line being added at end of teit table 
                        srow += 1 # increment number of stars now in table in table
#
#  Store data from VPHOT star line into teit star_row
#  teit format - because of VPHOT erratic star id numbering use B-V to identify standard stars - and allow for later
#       addition of TEIT_AUID list of  AUID's matching each row in TEIT
##
#       Column 0 -  B-V of reference star
#       Column 1-(2*cur_filt) - standard star reference mag and error - format U, Uerr, B, Berr, etc.
#       Column 2*num_filt +1 -> 2*num_filt + 3*cur_filt - machine mag, err, airmass - formt u,uerr,uairmass,b,berr,bairmass etc.
#
            cur_filt = teit_filters.index(currentfilter.upper())
# vphot_col_list = ["Vphot_Star_id","IM","SNR","X","Y","Sky","Air","B-V","Ref-mag","Target estimate","Active"]            
            teit[star_row, 0] = floatbv
            teit[star_row, 2*cur_filt + 1] = float(aline[vphot_col_list.index("Ref-mag")]) # Reference Mag
            if aline[vphot_col_list.index("Active")]  == "True" : # ensure good measurement
                teit[star_row, 2*num_filt + 3*cur_filt + 1] = float(aline[vphot_col_list.index("IM")]) # Instrument Mag
                teit[star_row, 2*num_filt + 3*cur_filt + 2] = 1/float(aline[vphot_col_list.index("SNR")].replace(" ","")) # instrument mag error
            teit[star_row, 2*num_filt + 3*cur_filt + 3] = float(aline[vphot_col_list.index("Air")]) # star air mass
#
#
#  Match B-V of reference field stars to AUID - store auid and reference star error mags (ref mags from VPHOT file - duplicate)
#
    num_test_stars = srow  # number of stars in VPHOT loaded field measured by user for this band
    if num_test_stars > max_num_test_stars :
        max_num_test_stars = num_test_stars # keep maximum number of test stars across loaded set of VPHOT images for teit max star number
    searchfield = "ra=" + searchra + "&dec=" + searchdec
    retrieve_std_mags()  # load standard mag information from AAVSO VSP data base
# global star_id_list,star_id_list_label,std_field_mags,std_field_star_count,searchfield,sf_col_list    
#            sf_col_list = ["RA","Dec","U","B","V","R","I"] # list names of each column in std_field_mags array

    teit_test_star_auid = []
    num_ref_stars = std_field_star_count # from standard field retrieval, number of reference stars
    for i in range(num_test_stars): # for each test star in table
        matchfound = "N"
#
#                
#  look for a stored reference magnitude and make sure it matches value in std_field_mags and a matching ref magnitude - looking out for matching B-V but not correct star
#                
        for f in range(len(img_set_filters)) :
            knownfilter = img_set_filters[f].upper()
            filter_index = teit_filters.index(knownfilter)
            for j in range(num_ref_stars):
                if (abs(teit[i,0] - (std_field_mags[j,sf_col_list.index("B")] - std_field_mags[j,sf_col_list.index("V")])) < .001 ) and (
                        abs(teit[i,2*filter_index + 1] - std_field_mags[j,sf_col_list.index(knownfilter)]) < .001 ) :   # look for match
                    for m in range(len(teit_filters)) : # for U,B,V,R,I
                        teit[i,2*m + 2] = std_field_mags[j,sf_col_list.index(teit_filters[m]) + 5] # store ref star error measures
                    teit_test_star_auid.append(star_id_list[j]) #  store AUID - fixing VPHOT problem!
                    matchfound = "Y"
                    break # go to next test star
            if matchfound == "Y":
                break # go to next test star
            else:
                 continue # try next filter
        if matchfound == "N":
            teit_test_star_auid.append("NoAUID")
            Errormsg("AUID match to star not found - 'NoAUID' will be identifier")
#    
#   Apply Extinction if requested
#
##
#  teit format - because of VPHOT erratic star id numbering use B-V to identify standard stars - and allow for later
#       addition of TEIT_AUID list of  AUID's matching each row in TEIT, teit[star,column]
##
#       Column 0 -  B-V of reference star
#       Column 1-(2*cur_filt) - standard star reference mag and error - format U, Uerr, B, Berr, etc.
#       Column 2*num_filt +1 -> 2*num_filt + 3*cur_filt - machine mag, err, airmass - formt u,uerr,uairmass,b,berr,bairmass etc.
#
#   
#   Test if extinction requested
#                    print("Entry extinction_setting = ",extinction_setting.get())
    if extinction_setting.get() == "Y" : 
#   Test if scope has extinction setup
#
            config_file = open("Photometry_Transform_Config_Data.txt","r") # open telescope info file
            for line in config_file:
                aline = []  # hold parsed line
                lineparse(line,aline,[";",";"]) # on ; is delimiter
#                print("\naline, telescopename, len(aline) ",aline,telescopename, len(aline))
#                print("aline[1], telescopename,len(aline)",aline[1], telescopename,len(aline))
                if (aline[1] == tel_id) and (len(aline) == 16): # found extinction record
                    ext_aline = aline # save all telescope data including extinction, observatory location
#                    print("ext_aline, ",ext_aline)
# Format of telescope line "ext_aline" -  #  'Telescope id';ex_tel_id;k'u;k'b;k'v;k'r;k'i;k"b,k"v,k"r,k"i,;obs_lat;obs_long;obs_elev;obslatdecimal;obslongdecimal,\n

                    kprime_u = aline[2]
                    kprime_b = aline[3]
                    kprime_v = aline[4]
                    kprime_r = aline[5]
                    kprime_i = aline[6]
                    kdblprime_b = aline[7]
                    kdblprime_v = aline[8]
                    kdblprime_r = aline[9]
                    kdblprime_i = aline[10]
                    break # valid extinction record
                elif aline[1] == tel_id : # means no extinction values set
                    Errormsg("Extinction Requested but telescope has no extinction setup\nSet Up at Extinction Settings and rerun")
                    return
# Apply extinction using VPHOT airmass
            kprime_list = [kprime_u,kprime_b,kprime_v,kprime_r,kprime_i]
            kdblprime_list = [0,kdblprime_b,kdblprime_v,kdblprime_r,kdblprime_i] # leading zero since no kdblprime_u
            num_report_stars = int(num_test_stars/10) + 1 # number of stars in report if requested
            if detailed_print_setting.get() == "Y":
                print(50*"*" + "\n              Extinction Verification Test Data - executed during transform testing VPHOT load - vphotload()\n")
                print("Current Extinction Coefficients -")
                print("\n\t\tk'u\tk'b\tk'v\tk'r\tk'i\n\t\t%s\t%s\t%s\t%s\t%s\n" % (kprime_u,kprime_b,kprime_v,kprime_r,kprime_i))
                print('\t\tk"b\tk"v\tk"r\n\t\t%s\t%s\t%s\n' % (kdblprime_b,kdblprime_v,kdblprime_r))
           
            for i in range(num_test_stars):
                printlines = "off"
                if float(i/num_report_stars) == int(i/num_report_stars) and detailed_print_setting.get() == "Y": # pick off stars for printing
                    printlines = "on"
                    print("\n\nStar AUID = ",teit_test_star_auid[i])
                    print("Filter\t Before\t After\t Diff\tAirmass\n\t Ext\t Ext")                            
                for j in range(len(kprime_list)) :  # also index of filters - u,b,v,r,i
                    if teit[i, 11 + 3*j] == 0 :  # test for measurement
                        continue # if none, go to next filter

                    save_pre_extinction = teit[i,11+3*j]
                    if j == len(kprime_list) : # if last entry on list
                        teit[i,11+3*j] = teit[i,11+3*j] - teit[i,11 + 3*j + 2] * float(kprime_list[j])  # apply first order extinction only for i filter until see if there is a way to handle
                    else:
                        teit[i,11+3*j] = teit[i,11+3*j] - float(kprime_list[j]) * teit[i,(11 + 3*j + 2)] - float(kdblprime_list[j])*teit[i, 11 + 3*j + 2]*(teit[i, 1 + 2*j] - teit[i, 1 + 2*(j+1)])
                    if printlines == "on" :
                        print("%s\t%7.3f\t%7.3f\t%7.3f\t%7.3f" % (teit_filters[j].lower(),save_pre_extinction,teit[i,11 + 3*j],teit[i,11+3*j]-save_pre_extinction,teit[i,11+3*j+2]))
            status_box.insert("end","\nExtinction Applied \t\tk'u\tk'b\tk'v\tk'r\tk'i\n\t\t%s\t%s\t%s\t%s\t%s\n" % (kprime_u,kprime_b,kprime_v,kprime_r,kprime_i))
            status_box.insert("end",'\t\tk"b\tk"v\tk"r\n\t\t%s\t%s\t%s\n' % (kdblprime_b,kdblprime_v,kdblprime_r))
    else:
        status_box.insert("end","\nNo Extinction Applied")
    radec = "RA = " + ra + "  Dec = " + dec
    text = "\n\nVPHOT Measurements Loaded for " + targetname + "\n" + radec 
    status_box.insert("end",text + "\n\n")
    text = "Image Dates - filters"
    status_box.insert("end",text + "\n")
    for i in range(len(obs_date)) :
        status_box.insert("end",obs_date[i] + "\n")
    status_box.see("end")
    transformtest.lift()
#    
#  Create list of transforms possible with filters submitted
#    Use color tranform nomenclature to track
#
    transforms_to_do = []
    if "u" in img_set_filters and "b" in img_set_filters:
        transforms_to_do.append("Tu_ub")
        transforms_to_do.append("Tb_ub")
    if "b" in img_set_filters and "v" in img_set_filters:
        transforms_to_do.append("Tb_bv")
        transforms_to_do.append("Tv_bv")
    if "v" in img_set_filters and "r" in img_set_filters:
        transforms_to_do.append("Tv_vr")
        transforms_to_do.append("Tr_vr")
    if "r" in img_set_filters and "i" in img_set_filters:
        transforms_to_do.append("Tr_ri")
        transforms_to_do.append("Ti_ri")
    if "v" in img_set_filters and "i" in img_set_filters:
        transforms_to_do.append("Tv_vi")
        transforms_to_do.append("Ti_vi")
        if "r" in img_set_filters:
            transforms_to_do.append("Tr_vi")
    if len(transforms_to_do) == 0 :
        Errormsg("Insufficient Filters for Any Analysis - reload images")
        
    if xforms_and_images_loaded == "N":
        xforms_and_images_loaded = "I"
    elif xforms_and_images_loaded == "T": # Transforms already loaded - activate analysis buttons
        xforms_and_images_loaded = "TI"
        perf_anal_btn.configure(state="active", bg="#E0FFFF", activebackground = "#E0FFFF")
        plot_xform_anal_btn.configure(state="active", bg="#E0FFFF", activebackground = "#E0FFFF")
        create_opt_btn.configure(state="active", bg="#E0FFFF", activebackground = "#E0FFFF")
        save_opt_btn.configure(state="active", bg="#E0FFFF", activebackground = "#E0FFFF")

    return
            
###################################################################################################
###################################################################################################
#
#    PLOT TRANSFORM ANALYSIS DATA - MAIN WINDOW CREATION
#
###################################################################################################
###################################################################################################
def xform_to_plot_pick(event):  # function executed when user selects transform to plot
    global xform_select_box,plot_data_full,final_transforms_to_do,max_num_test_stars,comp_star_id_list,test_xforms_float,test_xforms_str,allxforms,tel_id,std_field_name
    global annotate_tgt_setting
    xform_to_plot = xform_select_box.get()
    x = np.zeros((max_num_test_stars))
    y = np.zeros((max_num_test_stars))
    y1 = np.zeros((max_num_test_stars))
    bottom1 = np.zeros((6,2)) # for stack segment totals for bar plotting - index as next line
    group_count = np.zeros((6,2)) # for counting 0-.01,.01-.02, .02-.03, .03-.04, .04-.05, > .05 for untransformed (second index 0) and transformed (second index 1)
    y1err_data = np.zeros((max_num_test_stars))
    yerr_data = np.zeros((max_num_test_stars))
    xmin,xmax = 10,-10  # will force initial values
    plt.figure(figsize = (9,9) )
    color_list = ["b","g","r","c","m","y","k","b","g","r"]
    marker_list = ["o","1","2","3","4","s","*","+","x","D"]
#
#  Get transform coefficients used
#
    xform_color = "T" + xform_to_plot[3:5]
    x_axis_label = xform_to_plot[3:4] + "-" + xform_to_plot[4:5]  # e.g. b-v
    y_axis_label = xform_to_plot[1:2] # e.g. b
    color_xform = test_xforms_float[allxforms.index(xform_color)]
    mag_xform = test_xforms_float[allxforms.index(xform_to_plot)]
    for i in range(len(comp_star_id_list)):
        tgt_name = []
        for j in range(max_num_test_stars):
            x[j] = plot_data_full[i,j,transforms_to_do.index(xform_to_plot),1] # color difference tgt vs. comp  - e.g. (btgt - vtgt) - (bcomp - vcomp)
            if x[j] < xmin:
                xmin = x[j]
            if x[j] > xmax:
                xmax = x[j]
            y[j] = plot_data_full[i,j,transforms_to_do.index(xform_to_plot),0] # untransformed minus reference magnitude
            yerr_data[j] = plot_data_full[i,j,transforms_to_do.index(xform_to_plot),2] # untransformed minus reference magnitude instrument measurement error
            tgt_name.append(teit_test_star_auid[j])
        if detailed_print_setting.get() == "Y":
            print("x,y,yerr =",x,y,yerr_data)
        format1 = color_list[i] + marker_list[i]
        plt.errorbar(x,y,yerr = yerr_data, fmt = format1, elinewidth = 2, ecolor = color_list[i], label = comp_star_id_list[i])
        if annotate_tgt_setting.get() == "Y":
            for j in range(len(tgt_name)):
                plt.annotate(tgt_name[j][4:],xy = (x[j],y[j]), xytext = (x[j] + .01,y[j]))
#    
#  Plot Data
#
    plt.legend(bbox_to_anchor=(.90,1), loc = 0)
    y_val_xmin = -mag_xform * color_xform * xmin # predicted error = negative error correction
    y_val_xmax = - mag_xform * color_xform * xmax
    plt.plot([xmin,xmax],[y_val_xmin,y_val_xmax],linestyle='-',label = "Predicted Error")
    plt.plot([xmin,xmax],[y_val_xmin - .02, y_val_xmax - .02],linestyle = ":")
    plt.plot([xmin,xmax],[y_val_xmin + .02, y_val_xmax + .02],linestyle = ":")

    text = ("Telescope - " + tel_id + "   Field - " + std_field_name + "     Transforms - " + xform_to_plot + " = %7.3f    " + xform_color + " = %7.3f") % (mag_xform,color_xform)
    text1 = ("Predicted Line = - " + xform_color + " * " + xform_to_plot + " * (Tgt/Comp Color Difference)" + "\n\n")
    plt.title("\n" + text + "\n" + text1)
    plt.xlabel("Color Difference [ (" + x_axis_label + ")tgt - ("  + x_axis_label + ")comp ]")
    plt.ylabel(y_axis_label + " Filter Untransformed Magnitude Minus Reference Magnitude" )
#
#  Plot number of measuremtns within .01 deltas from ref mag both before and after transform
#
    
    plt.figure(figsize = (9,9))
    
# group_ count  for counting 0-.01,.01-.02, .02-.03, .03-.04, .04-.05, > .05 for untransformed (second index 0) and transformed (second index 1)    
    for i in range(len(comp_star_id_list)):
        for j in range(max_num_test_stars):
            xf_delta_meas = abs(plot_data_full[i,j,transforms_to_do.index(xform_to_plot),3]) # transformed minus reference magnitude
            not_xf_delta_meas = abs(plot_data_full[i,j,transforms_to_do.index(xform_to_plot),0]) # not transformed minus reference magnitude
            if detailed_print_setting.get() == "Y":
                print("xf_delta_meas,not_xf_delta_meas ",xf_delta_meas,not_xf_delta_meas)
            for k in range(5):
                if (not_xf_delta_meas > k/100.0) and (not_xf_delta_meas <= (k+1)/100.0) :
                    group_count[k,0] += 1
                    
                if xf_delta_meas > k/100.0 and xf_delta_meas <= (k+1)/100.0 :
                    group_count[k,1] += 1
            if not_xf_delta_meas > 0.05 :
                group_count[5,0] +=1
            if xf_delta_meas > 0.05 :
                group_count[5,1] += 1
    
    bar_locations = np.arange(2)
    p1 = plt.bar(bar_locations,group_count[0,],color = 'r')
    bottom1[0,] = group_count[0,]
    p2 = plt.bar(bar_locations,group_count[1,],bottom = bottom1[0,],color = 'b')
    bottom1[1,] = bottom1[0,] + group_count[1,]
    p3 = plt.bar(bar_locations,group_count[2,],bottom = bottom1[1,],color = 'g')
    bottom1[2,] = bottom1[1,] + group_count[2,]
    p4 = plt.bar(bar_locations,group_count[3,],bottom = bottom1[2,],color = 'c')
    bottom1[3,] = bottom1[2,] + group_count[3,]
    p5 = plt.bar(bar_locations,group_count[4,],bottom = bottom1[3,],color = 'm')
    bottom1[4,] = bottom1[3,] + group_count[4,]
    p6 = plt.bar(bar_locations,group_count[5,],bottom = bottom1[4,],color = 'y')
    bottom1[5,] = bottom1[4,] + group_count[5,]
    labels = [] 
    for i in range(5):
        limits = (("%4.2f - %4.2f") % (i/100.0,(i+1)/100.0))
        labels.append(limits)
    labels.append((" > %4.2f") % (0.05))
    for j in range(2) :
        for i in range(6):
            if group_count[i,j] != 0:
                if i == 0:
                    plt.text(j,bottom1[0,j]/2,str(int(group_count[0,j])) + " cases within " + labels[0] + " mag",va="center", ha="center")
                elif i < 5:
                    plt.text(j,(bottom1[i-1,j] + group_count[i,j]/2), str(int(group_count[i,j])) + " cases within " + labels[i] + " mag", va="center", ha="center")
                else:
                    plt.text(j,(bottom1[i-1,j] + group_count[i,j]/2), str(int(group_count[i,j])) + " cases " + labels[i] + " mag", va="center", ha="center")
    plt.title("Difference of Reference Mags with Untransformed and Transformed Observations\n" + text)
    plt.xlabel("Untransformed                                                                       Transformed",ha="center")
    plt.ylabel("Number of Test Cases")
    plt.xticks([])
    plt.show() 
    
    return


    
def plot_xform_anal(): # main window creation program for plotting transform analysis information
    global plot_data,max_num_test_stars,teit,final_transforms_to_do,comp_star_setting,detailed_print_setting,xform_select_box,comp_star_id_list,plot_data_full,annotate_tgt_setting
    global num_plot_comps

    plot_xform_window = Toplevel()
    plot_xform_window.title("Plot Transform Test Data - " + version)
    w, h = root.winfo_screenwidth(), root.winfo_screenheight()
    plot_xform_window.geometry("%dx%d+0+0" % (.9*w, .9*h))
    info = Label(plot_xform_window,text = "Current test field and transforms will be tested with different comp stars\nDetails of each run will show in Status Box on Prevous Screen (Test Transform Coefficients Window\n ",font=16)
    info.grid(row=0,column = 0, columnspan = 2)
    
 
#
#  determine set of comp stars to use in analysis for plotting
#
#   See if user wants one comp or max comps
#
#Label(transformtest, text = "Plots - number of comps", font = 16).grid(row=2,column=4, sticky = E) # widen column 5 for next radiobuttons
#    num_plot_comps = StringVar()
#    num_plot_comps.set("Max")
#    Radiobutton(transformtest,text= " 1 ",value = "1",font=12,variable = num_plot_comps).grid(row=2,column=5,sticky = E)
#    Radiobutton(transformtest,text= "Max (<=10)",value = "Max",font=12,variable = num_plot_comps).grid(row=2,column=6,sticky = W)
    if num_plot_comps.get() == "Max" :
        flen = 5 # number of filters
        comp_star_id_list = []
        plot_data_full = np.zeros((10,max_num_test_stars,11,5)) # sized to maximum number of transforms possible (11)
        count = 0
        for i in range(max_num_test_stars):
            for j in range(flen): #range(5) : # all filters
                if teit[i,2*j+2] == 0 : # go to next star if star doesn't have reference values for all filters
                    break
            comp_star_id_list.append(teit_test_star_auid[i])
            count += 1 # count number of comp stars found
            if count == 10:  # take first 10 stars with data on all filters - may change later to be more selective in fields with large number of stars
                break
        num_comp_stars = count # save number of comp stars
        comp_star_setting.set("AUID") # set so analyze transforms will use AUID
        for n in range(num_comp_stars):
            auid_comp_star.set(comp_star_id_list[n])
            analyze_transforms()
    #        
    #  save plot values
    #
            for i in range(max_num_test_stars):
                for j in range(len(final_transforms_to_do)):
                    for k in range(5):
                        plot_data_full[n,i,j,k] = plot_data[i,j,k] # comp star number, tiet star number, transforms index in final_transforms_to_do,
    #                            0 difference between untransformed mag and reference mag - 1= color difference star vs comp -delta(b-v) - 2= untransformed instrument mag measurement error
                    if detailed_print_setting.get() == "Y":
                        print("compstar[n],n,i,j,plot_data_full[n,i,j,] %s %s %d  %d  %d %7.3f  %7.3f  %7.3f " % (comp_star_id_list[n],comp_star_id_list[i],n,i,j,plot_data_full[n,i,j,0],plot_data_full[n,i,j,1],plot_data_full[n,i,j,2]))
    else:  # User only wants one comp star that they selected
        compid = analyze_transforms() # this will select option defining comp star to use - and return comp star id
        num_comp_stars = 1
        plot_data_full = np.zeros((1,max_num_test_stars,11,5)) # sized to maximum number of transforms possible (11)
        comp_star_id_list = []
        comp_star_id_list.append(compid)

    #        
    #  save plot values
    #
        for i in range(max_num_test_stars):
            for j in range(len(final_transforms_to_do)):
                for k in range(5):
                    plot_data_full[0,i,j,k] = plot_data[i,j,k] # comp star number, tiet star number, transforms index in final_transforms_to_do,
#                            0 difference between untransformed mag and reference mag - 1= color difference star vs comp -delta(b-v) - 2= untransformed instrument mag measurement error
                if detailed_print_setting.get() == "Y":
                    print("compstar[n],n,i,j,plot_data_full[n,i,j,] %s %s %d  %d  %d %7.3f  %7.3f  %7.3f " % (comp_star_id_list[0],comp_star_id_list[i],0,i,j,plot_data_full[0,i,j,0],plot_data_full[0,i,j,1],plot_data_full[0,i,j,2]))

#
#   Add dropdown combo box allowing selection of transform to plot
#
        
    Label(plot_xform_window, text = "Annotate Plot with Target Star AUID ?",font=16).grid(row=1,column = 0, sticky = E)
    annotate_tgt_setting = StringVar()
    annotate_tgt_setting.set("N") # set default
    Radiobutton(plot_xform_window, text = "Yes", value = "Y", font=12, variable = annotate_tgt_setting).grid(row=1,column=1,sticky=W)
    Radiobutton(plot_xform_window, text = "No", value = "N", font=12, variable = annotate_tgt_setting).grid(row=1,column=1,sticky=E)
    
    
    
    
    
    
    Label(plot_xform_window, text = " ",font=12).grid(row=2,column=0)
    Label(plot_xform_window,text = "Select Transform to plot",font=16,bg="#E0FFFF").grid(row=3,column=0,sticky = "E")
    xform_to_plot_var = StringVar()
    xform_select_box = ttk.Combobox(plot_xform_window,width=12,textvariable=xform_to_plot_var,values=final_transforms_to_do,font=16)
    xform_select_box.state(['readonly'])
    xform_select_box.bind("<<ComboboxSelected>>",xform_to_plot_pick)
    xform_select_box.current(0)
    xform_select_box.grid(row=4,column=1)
    
    
    
    return
    











def test_transforms():
    global transformtest,teit_filters,num_filt,teit,tat,tat_col_ref,test_xforms_float,test_xforms_str,allxforms
    global test_xforms_err_str, test_xforms_err_float,status_box,detailed_print_setting,save_opt_btn,comp_star_setting,auid_comp_star
    global num_plot_comps,create_opt_btn, perf_anal_btn, plot_xform_anal_btn
#
#  Define Major Tables for testing transforms
#
#  teit = Transform Evaluation Input Table - numpy array
#    teit_filters = ["U","B","V","R","I"]  # set up to allow easy program additions for other fiters
#    num_filt = len(teit_filters)  # number of filters
##
#  teit format - because of VPHOT erratic star id numbering use B-V to identify standard stars - and allow for later
#       addition of TEIT_AUID list of  AUID's matching each row in TEIT
##
#       Column 0 -  B-V of reference star
#       Column 1-(2*cur_filt) - standard star reference mag and error - format U, Uerr, B, Berr, etc.
#       Column 2*num_filt +1 -> 2*num_filt + 3*cur_filt - machine mag, err, airmass - formt u,uerr,uairmass,b,berr,bairmass etc.
#
# 
#   tat = Transform Analysis Table
#
#       Column 0 - B-V of reference star
#       Column 1 - xform identifier (Ta_bc) where a is filter and bc color filters
#       Column 2 - [(0)untransformed mag; (1)untransformed mag error; (2)transformed mag;(3)transformed mag error;
#                  (4)reference minus untransformed mag;(5)reference minus untransformed mag error;
#                  (6)reference minus transformed mag; (7)reference minus transformed mag error]
#
#    Inirialize

#    teit = np.zeros((500,5*num_filt + 1)) # allow up to 500 reference stars - maybe change later to count
#    test_xforms_float = np.zeros(len(allxforms)) # float of transform values in sequence of allxforms

# Create window    
    transformtest = Toplevel()
    transformtest.title("Test Transform Sets With Standard Field - " + version)
    w, h = root.winfo_screenwidth(), root.winfo_screenheight()
    transformtest.geometry("%dx%d+0+0" % (.9*w, .95*h))
    tf_menubar = Menu(transformtest)
    transformtest.config(menu=tf_menubar)
    tf_menubar.add_command(label="Extinction Settings", command=extinction)
    Label(transformtest, text = "1. Set Up Test Data",font=16).grid(row=0,column=0,columnspan=2,sticky = W)
    Button(transformtest,text="Load VPHOT files of Standard Field \nto use for test - 5 or less files",font=16,command=vphotload,bg="#E0FFFF", activebackground = "#E0FFFF").grid(row=0,column=1,columnspan=2,padx=2, sticky = W)
#    Label(transformtest, text="Load or enter Transform Coefficients: ",font=12).grid(row=1,column=2,sticky = "E",pady=5)
    Button(transformtest,text="Load Transform Coefficients\nusing .ini file (TA Format)",font=16,command=loadini,bg="#E0FFFF", activebackground = "#E0FFFF").grid(row=0,column=3,padx=2, sticky = W)
    Label(transformtest, text = "or",font = 16).grid(row = 0, column = 4, sticky = W)
    Button(transformtest,text="Type in transform\ncoefficients",font=16,command=entertransforms,bg="#E0FFFF", activebackground = "#E0FFFF").grid(row=0,column=4,padx=5, sticky = E)
    
    Label(transformtest, text = "2. Perform Test", font = 16).grid(row=1,column = 0,columnspan = 2, sticky = W)
    perf_anal_btn = Button(transformtest, text = "Transform Analysis\nStatistical",font=16,command=analyze_transforms,bg="#E0FFFF", activebackground = "#E0FFFF",state="disabled")
    perf_anal_btn.grid(row=1,column=1,padx = 2, sticky = W)
    plot_xform_anal_btn = Button(transformtest, text = "Transform Analysis\nPlots",font=16,command=plot_xform_anal,bg="#E0FFFF", activebackground = "#E0FFFF", state = "disabled")
    plot_xform_anal_btn.grid(row=1,column=2,padx = 2, sticky = W)

    
    Label(transformtest, text = "Select Comp Star: ",font=12).grid(row=2,column = 0, sticky = E)
    comp_star_setting = StringVar()
    comp_star_setting.set("Ensemble") # set default
    Radiobutton(transformtest, text = "Ensemble", value = "Ensemble", font=12, variable = comp_star_setting).grid(row=2,column=1)
    Radiobutton(transformtest, text = "Star with min err", value = "MinError", font=12, variable = comp_star_setting).grid(row=2,column=2)
    Radiobutton(transformtest, text = "Star auid", value = "AUID", font=12, variable = comp_star_setting).grid(row=2,column=3,sticky=W)
    auid_comp_star = StringVar()
    auid_comp_star.set("Enter AUID ")
    g = Entry(transformtest,textvariable = auid_comp_star, font=12,width=11)
    g.grid(row=2,column=3,sticky = E)
    
#    l1 = Label(transformtest, text = "_               _" ",font=12).grid(row=1,column=5) # widen column 5 for row 2 radiobuttons
    Label(transformtest, text = "Plots - number of comps", font = 16).grid(row=2,column=4, sticky = E) # widen column 5 for next radiobuttons
    num_plot_comps = StringVar()
    num_plot_comps.set("Max")
    Radiobutton(transformtest,text= " 1 ",value = "1",font=12,variable = num_plot_comps).grid(row=2,column=5,sticky = E)
    Radiobutton(transformtest,text= "Max (<=10)",value = "Max",font=12,variable = num_plot_comps).grid(row=2,column=6,sticky = W)

    Label(transformtest, text = "Show Detailed \n  transform/star data  ",font=12).grid(row=3,column = 0, sticky = E)
    detailed_print_setting = StringVar()
    detailed_print_setting.set("N")  # set default not to print details of transform test for every star/transform
    Radiobutton(transformtest, text= "Yes", value = "Y",font=12, variable = detailed_print_setting).grid(row=3,column=1,sticky=W)
    Radiobutton(transformtest, text= "No", value = "N", font =12, variable = detailed_print_setting).grid(row=3,column=1,sticky=E)
 
    Label(transformtest, text = "3. Transform Optimization\n    (optional - under test)", font=16).grid(row=4,column=0, columnspan = 1, sticky = W)
    create_opt_btn=Button(transformtest, text = "Create Optimized \nTransform Set",font=16,command=optimize_transforms,bg="#E0FFFF",activebackground = "#E0FFFF", state = "disabled")
    create_opt_btn.grid(row=4,column=1,padx=2)
    save_opt_btn = Button(transformtest, text = "Save Optimized\n   Transforms",font=16,command=save_opt_xforms,bg="#E0FFFF", activebackground = "#E0FFFF", state="disabled")
    save_opt_btn.grid(row=4,column=2,padx = 2)
    
                                 
               
           
    status_box = tkst.ScrolledText(transformtest,width=120,height=35,wrap=WORD,font=16)
    status_box.grid(row=5,column=0,columnspan = 12, rowspan = 12,pady = 2)
    status_box.insert("end","          STATUS INFORMATION")
    status_box.insert("end","\n\nTransform equations used are from the AAVSO CCD Manual:\n(1)  Vvar = delta(v) + Tv_bv * delta(B-V) + Vcomp\n(2)  delta(B-V) = Tbv * delta(b-v)\n( Upper case  are published reference magnitudes, lower case are instrumental magnitudes)\n")
               
    return



###################################################################################
###################################################################################
##                                                                               ##
##                    Main Program                                               ##
##                                                                               ##
###################################################################################
###################################################################################
# Main Program functions
def myfunction(event): 
    canvas1.configure(scrollregion=canvas1.bbox("all"))

#  Main Program

version = " - Version TG_V7.2"
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
menubar = Menu(root)
root.config(menu=menubar)
menubar.add_command(label="Extinction Settings", command=extinction)
detailed_print_setting = StringVar()
detailed_print_setting.set("N")  # set default not to print details 
xform_manual_entry_started = 0  # set up for testing transforms allowing typed transforms to be saved for one session
xforms_and_images_loaded = "N" # set up indicator if anlysis data loaded - N=none,I=images,T=Transforms,TI = images and transforms
allxforms = ["Tub","Tu_ub","Tb_ub","Tbv","Tb_bv","Tv_bv","Tvr","Tv_vr","Tr_vr","Tri","Tr_ri","Ti_ri","Tvi","Tv_vi","Ti_vi","Tr_vi"] # set up master xform list
# Set up master close window handler  WINDOWS UNIQUE CODE
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
tel_id_box = ttk.Combobox(app,width=12,textvariable=tel_id_picked_var,values=tel_id_list,font=12)
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
fmt_name.set("VPHOT")
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
extinction_setting = StringVar()
extinction_setting.set("N")
Label(app,text = "Extinction", font =10).grid(row=9,column=2)
Radiobutton(app,text= "On", value = "Y",font=10, variable = extinction_setting).grid(row=8,column=2,sticky=W)
Radiobutton(app, text= "Off", value = "N", font =10, variable = extinction_setting).grid(row=8,column=2,sticky=E)


# Create Button to save transforms - disabled
save_xform_button = Button(app,text="Save Transform Set")
save_xform_button.configure(state = "disabled", command = savetransforms,font=12)
save_xform_button.grid(row=8,column=4,padx=20)

# Create button to merge results of different observations
merge_obs_sets_button = Button(app,text="Review / Average\n Transform Sets")
merge_obs_sets_button.configure(command = mergesets,state = "disabled",font=12)
merge_obs_sets_button.grid(row=8,column=5,padx=20)

# Create button to delete of transform sets
delete_obs_sets_button = Button(app,text="Delete Old \nTransform Sets")
delete_obs_sets_button.configure(command = deletesets,state = "disabled",font=12)
delete_obs_sets_button.grid(row=8,column=6,padx=20)

# Create button to Test Transforms
test_transform_set_button = Button(app,text="Test Transform Set")
test_transform_set_button.configure(command = test_transforms,state = "disabled",font=12)
test_transform_set_button.grid(row=8,column=7,padx=20)
# size window
w, h = root.winfo_screenwidth(), root.winfo_screenheight()
# use the next line if you also want to get rid of the titlebar
root.geometry("%dx%d+0+0" % (.9*w, .7*h))
root.mainloop()



