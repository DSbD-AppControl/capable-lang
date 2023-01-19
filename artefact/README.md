# Capable

<!-- TODO Add blurb -->

This artefact comprises of the proof-of-concept language (as realised in Idris2), and the test suite used.

## Manifest

The artefact is approx. 300M in size.

Specifically the obtained archive contains the following:

1. `capable.box` :: A Virtual Box virtual machine that contains Capable's source code & test suite;
2. `capable.tar.gz` :: A copy of Capable's source code, and generated IdrisDoc;
3. `capable_doc.tar.gz` :: A copy of the IdrisDoc for the coding project;
4. `capable_html.tar.gz` :: A copy of the katla generated html showing semantically highlighted code;
4. `capable.pdf` :: A copy of the submitted paper;

## About the Submission

Our paper describes the realisation of Capable as both an *Embedded Domain Specific Language* (EDSL) and *Domain Specific Language* (DSL) in Idris2.
We follow standard constructions and idioms for working with the Idris family of languages and present a self-contained coding project.
Instructions are provided in `INSTALL.md` to build/test the project, together with information on how to obtain Idris2 and the version required.

## Mechanisation

The source code is divided into three main module hierarchies:

### Toolkit

The module `Toolkit` contains helper code and constructs required for decapableping Capable.

### Capable

+ `Capable.Terms`

  + ...

+

### Exemplars

We provide a test suite containing sample Capable code.

## Artifact Requirements

The artefact has been packaged as a **Virtual Box image** using packer, and has been designed to be run using **Vagrant**.

+ https://www.virtualbox.org/

+ https://www.vagrantup.com/

We provide salient details about the virtual machine to establish an indicative set of minimal requirements to record the *environment at the time of submission* that the software would run in.

| Base OS  | Alpine Linux 3.16.x |
| CPU      | 64-AMD              |
| Memory   | 4 GB                |
| Disk     | 2 GB                |
| Cores    | 2                   |
| Idris2   | 0.6.x               |
| Username | idris-playground    |
| Password | idris-playground    |

Other notable installed software on the virtual machine include:

+ `mg` A lightweight emacs clone for source file browsing;
+ `tmux` For advanced remote terminal usage;

### Alternative Interaction

Alternatively, we have provided the raw sources for the software code along side the virtural machine box.
To run these sources you will need a working installation of: **Idris2**, **Hyperfine**, and **Make**.
Details of installing the software code can be found in `INSTALL.md`, located in the top-level directory of the software code.

## Getting Started

### Box Installation

Once the required dependencies have been installed, the following instructions will provide you with a working environment to interact with the software code.

These instructions have been tested on a standard Linux desktop, for example an Ubuntu LTS release.

1. Extract the box named `capable.box` from the archive, and place it inside a directory of your choosing.
   We recommend the `Downloads` folder.
1. Create a separate working directory called `capable` in a location of your choice, and navigate to it using your preferred command prompt.
1. Assuming that the box is located in your `Downloads` folder, register the box with vagrant using:

```{bash}
vagrant box add $HOME/Downloads/capable.box --name capable
```

1. Within `capable` we can instantiate the vagrant project with the registered box using:

```{bash}
vagrant init capable
```

   This will create a project in the called directory, signified by the creation of a configuration file called: `VagrantFile`.

1. The Box has been initialised with a non-standard username/password combination.
   To enable a clean interaction with the box we can augment the configuration file `VagrantFile` within `capable` using:

```
config.ssh.username = "idris-playground"
config.ssh.password = "idris-playground"
config.vm.synced_folder ".", "/vagrant", disabled: true
```

More instructions are available on the [Vagrant website](https://www.vagrantup.com/docs/vagrantfile/ssh_settings.html).

1. We can then reload the specification using: `vagrant reload`

### Box Interaction

We can interact with the Box from the vagrant project within `capable`, using the following commands:


+ Starting the box: `vagrant up`
+ Halting the box: `vagrant halt`
+ Accessing the box: `vagrant ssh`

### Building the Artifact

From the session established by vagrant (ssh):

1. Navigate to the folder `capable`

2. The type-checker can be built, and examples type-checked, using:

   1. `make capable`
   2. `make capable-test-run`

#### Problems

Should one encounter any problems, then the command `make clean` can be used to remove build files.

### Browsing Source Files

The source files have been provided alongside the virtual machine to enable better viewing of the source.
Specifically, the following sub-directories are of interest:

+ `capable` Contains the source code for the framework and the examples in appropriate directories.
+ `capable_doc` Generated idrisdoc documentation for documented elements.
+ `capable_html` Katla generated html providing pretty view of the source code sans the need for a text editor.

### Interacting & Reusability

To play with the language we recommend extending the test suite with a new folder, or creating examples and calling the executable by hand.
The executable will be located in `./build/exec/capable`.

For information on the language's syntax, one can study the examples within the test suite.

<!-- EOF -->
