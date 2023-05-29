# ICFP 2023 Artifact

Name:    Etna: An Evaluation Platform for Property-Based Testing

## Artifact Instructions

### Language Dependencies

These steps should already be completed in the VM.

1. For Python, install version 3.10.5, 
   and make sure `python3` points to this version.

2. For Haskell, install `stack`:
   ```
   $ curl -sSL https://get.haskellstack.org/ | sh
   ```

3. For Coq, [TODO].

### Package Dependencies

These steps should already be completed in the VM.

1. For Python, make sure you have `pip` installed.

   Then, run the following commands:
   ```
   $ cd ~/etna
   $ make install
   ```

2. For Haskell, run the following commands:
   ```
   $ cd ~/etna/bench-suite/Haskell/BST
   $ stack ghci src/Impl.hs
   ```

   Doing this for the first time will force `stack` to 
   install GHC 9.0.2 and the required packages.

3. For Coq, [TODO].

### Experiment Replication

Running our experiments in full as we did originally for the paper 
would take several days in total. As such, we offer scaled-down 
versions that should demonstrate the same trends but take drastically 
less time. The `Makefile` is configured to run these versions by default. 
To instead run the full experiment, just add the `--full` flag.

Estimated times are rough estimates.

#### Section 4.1: Comparing Frameworks.

Estimated time for scaled-down experiment:

#### Section 4.2: Exploring Size Generation.

Estimated time for scaled-down experiment: around 1.5 hours.

While we originally ran 100 trials for each task, the analysis for
the experiment only focuses on three tasks. So, this version runs the 
full 100 trials for the three tasks and 10 trials for the other tasks.

Run this to collect the data for this experiment:
```
make collect4.2
```
The raw JSONs will be saved in `data/4.2`.

Run this to analyze the data for this experiment:
```
make analyze4.2
```

Please view the chart `figures/figure2.png`. This should resemble
Fig. 2 from the paper, though with colors instead of numbered labels.

As in the paper, the task #1 trendline (red) should have the steepest
upward trajectory. The task #2 trendline (green) should also go up,
but less steeply. The task #3 trendline (blue) should be mostly flat
and near the y-axis.

Note that the precise y-axis numbers may differ from the paper — there
is variance due to the random nature of these generation strategies. 
However, the relative trends described above should hold.

#### Section 4.3: Enumerator Sensitivity.

## QEMU Instructions

The ICFP 2023 Artifact Evaluation Process is using a Debian QEMU image as a
base for artifacts. The Artifact Evaluation Committee (AEC) will verify that
this image works on their own machines before distributing it to authors.
Authors are encouraged to extend the provided image instead of creating their
own. If it is not practical for authors to use the provided image then please
contact the AEC co-chairs before submission.

QEMU is a hosted virtual machine monitor that can emulate a host processor
via dynamic binary translation. On common host platforms QEMU can also use
a host provided virtualization layer, which is faster than dynamic binary
translation.

QEMU homepage: https://www.qemu.org/

### Installation

#### OSX
``brew install qemu``

#### Debian and Ubuntu Linux
``apt-get install qemu-kvm``

On x86 laptops and server machines you may need to enable the
"Intel Virtualization Technology" setting in your BIOS, as some manufacturers
leave this disabled by default. See Debugging.md for details.

#### Arch Linux

``pacman -Sy qemu``

See the [Arch wiki](https://wiki.archlinux.org/title/QEMU) for more info.

See Debugging.md if you have problems logging into the artifact via SSH.

#### Windows 10

Download and install QEMU via the links at

https://www.qemu.org/download/#windows.

Ensure that `qemu-system-x86_64.exe` is in your path.

Start Bar -> Search -> "Windows Features"
          -> enable "Hyper-V" and "Windows Hypervisor Platform".

Restart your computer.

#### Windows 8

See Debugging.md for Windows 8 install instructions.

### Startup

The base artifact provides a `start.sh` script to start the VM on unix-like
systems and `start.bat` for Windows. Running this script will open a graphical
console on the host machine, and create a virtualized network interface.
On Linux you may need to run with `sudo` to start the VM. If the VM does not
start then check `Debugging.md`.

Once the VM has started you can login to the guest system from the host.
Whenever you are asked for a password, the answer is `password`. The default
username is `artifact`.

```
$ ssh -p 5555 artifact@localhost
```

You can also copy files to and from the host using scp.

```
$ scp -P 5555 artifact@localhost:somefile .
```

### Shutdown

To shutdown the guest system cleanly, login to it via ssh and use

```
$ sudo shutdown now
```

### Artifact Preparation

Authors should install software dependencies into the VM image as needed,
preferably via the standard Debian package manager. For example, to install
GHC and cabal-install, login to the host and type:

```
$ sudo apt update
$ sudo apt install ghc
$ sudo apt install cabal-install
```

If you really need a GUI then you can install X as follows, but we prefer
console-only artifacts whenever possible.

```
$ sudo apt install xorg
$ sudo apt install xfce4   # or some other window manager
$ startx
```

See Debugging.md for advice on resolving other potential problems.

If your artifact needs lots of memory you may need to increase the value
of the `QEMU_MEM_MB` variable in the `start.sh` script.

When preparing your artifact, please also follow the [Submission
Guidelines](https://icfp23.sigplan.org/track/icfp-2023-artifact-evaluation#Submission-Guidelines).
