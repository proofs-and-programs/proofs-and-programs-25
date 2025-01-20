# proofs-and-programs-25
Code for the course "Proofs and Programs", January 2025, IISc

### This repository uses SaveMyAss(ignments)

*SaveMyAss* allows students to continue working with a fork of this repository to save their work, without having to worry about accidentally pushing their (clear text) solutions to their public fork &mdash; protecting them from accidental plagiarism! Check out the [repository](https://github.com/mrigankpawagi/SaveMyAss) for more information.

#### Setup

> [!NOTE]
> You must have Python 3.7+ installed on your machine.

Once you fork this repository and clone it to your local machine, run `python .savemyass/setup_savemyass.py` from the root of the repository to launch the setup wizard. The wizard will ask you to provide the Python command to run on your machine and a secret passkey to encrypt your assignment files.

If you have previously set up SaveMyAss and are cloning the repository again, you must provide the same secret passkey as your previous setup to decrypt the files. The setup wizard will decrypt the files for you.

#### Uninstall

To uninstall SaveMyAss and push the clear text files to your repository, run `python .savemyass/freemyass.py` from the root of the repository. This will remove git-hooks, decrypt assignment files, and destroy your secret passkey.

#### How it works

SaveMyAss installs git hooks that intercept commits and checkout operations. When you commit any assignment file, it encrypts the file using your secret passkey before adding it to the commit. You can then safely push your changes to your public repository. However, you will continue to see the unencrypted file in your working directory. Similarly, when you pull changes from your public repository, SaveMyAss decrypts any encrypted assignment files using your secret passkey.
