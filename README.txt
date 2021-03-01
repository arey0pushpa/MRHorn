We assume you have the following softwares installed:

1. OR Tools.  
  Follow: https://developers.google.com/optimization/install
  
  $ python -m pip install --upgrade --user ortools
 
  This requires Python (version 3.5+ on Linux, or 3.6+ on Mac OS or Windows), 
  and the Python package manager PIP.
  
  In case you have not already have PIP installed:
  Follow: https://pip.pypa.io/en/stable/installing/

  $ sudo apt-get install python3-pip

2. pysat.
   Follow: https://github.com/pysathq/pysat 
    
  You may also need libz-dev:
   $ sudo apt-get install libz-dev

   $ pip3 install python-sat[pblib,aiger]
 
There can be numerous problem with pip. Either due to old pip, 
resulting in unable to install aiger for pysat or just due to incompatiblility. 
In that case Follow : https://stackoverflow.com/questions/49836676/error-after-upgrading-pip-cannot-import-name-main

