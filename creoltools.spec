Summary:	Environment for the Creol Language
Name:		creoltools
Version:	0.0g
Release:	0%{?dist}
Vendor:		Universitetet i Oslo
URL:		http://creol.berlios.de/
License:	GPLv3+
Group:		Development/Languages
BuildRoot:	%{_tmppath}/%{name}-root
Source0:	%{name}-%{version}.tar.bz2

BuildRequires: ocaml >= 3.09
BuildRequires: ocaml-findlib
BuildRequires: /usr/bin/texi2pdf
BuildRequires: ocaml-libxml2
Requires: maude >= 2.2
Requires(post): /sbin/install-info
Requires(preun): /sbin/install-info

%description
The creol tools currently provide an emacs mode for writing Creol programs,
a compiler from Creol to the creol interpreter in Maude, and the semantics
in Maude.

%prep
%setup -q

%build
# We have no need to hurry.
%configure OCAMLOPT_FLAGS="-inline 10"
make

# Build the pdf, because most people seem to prefer hard copy stuff.
make pdf

%check
make check

%install
rm -rf %{buildroot}
%makeinstall

# If we succeeded in building native versions, we only package this version,
# otherwise we distribute the byte code version.
for i in creolc ; do
    if [ -x %{buildroot}%{_bindir}/$i.opt ] ; then
        mv %{buildroot}%{_bindir}/$i.opt %{buildroot}%{_bindir}/$i
	strip %{buildroot}%{_bindir}/$i
    fi
done

# install-info dumps a dir file
rm -f %{buildroot}%{_infodir}/dir

# Now generate the fedora specific configuration.
mkdir -p %{buildroot}%{_sysconfdir}/profile.d
cat > %{buildroot}%{_sysconfdir}/profile.d/creol.sh << EOF
test -f %{_sysconfdir}/profile.d/maude.sh && \
  source %{_sysconfdir}/profile.d/maude.sh
MAUDE_LIB=\${MAUDE_LIB:+\${MAUDE_LIB}:}%{_datadir}/%{name}
export MAUDE_LIB
EOF
chmod 0644 %{buildroot}%{_sysconfdir}/profile.d/creol.sh

%clean
rm -rf %{buildroot}

%post
/sbin/install-info %{_infodir}/%{name}.info %{_infodir}/dir || :

%preun
if [ $1 = 0 ] ; then
    /sbin/install-info --delete %{_infodir}/%{name}.info %{_infodir}/dir || :
fi

%files
%defattr(-,root,root)
%doc AUTHORS COPYING NEWS README README-alpha info/creoltools.pdf
%{_bindir}/creolc
%{_bindir}/creolbug
%{_bindir}/creolshell
%dir %{_datadir}/%{name}
%{_datadir}/%{name}/*
%{_infodir}/*.info*
%config(noreplace) %{_sysconfdir}/profile.d/creol.sh

%changelog
* Thu Apr 17 2007 Marcel Kyas <kyas@ifi.uio.no> - 0.0b-0
- Initial build
