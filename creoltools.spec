%define opt %(test -x %{_bindir}/ocamlopt && echo 1 || echo 0)
%define debug_package %{nil}

Summary:	Environment for the Creol Language
Name:		creoltools
Version:	0.0h
Release:	0%{?dist}
Vendor:		Universitetet i Oslo
URL:		http://creol.berlios.de/
License:	GPLv3+
Group:		Development/Languages
BuildRoot:	%{_tmppath}/%{name}-%{version}-%{release}-root-%(%{__id_u} -n)
Source0:	%{name}-%{version}.tar.bz2

BuildRequires: ocaml >= 3.09
BuildRequires: ocaml-findlib-devel
BuildRequires: /usr/bin/texi2pdf
BuildRequires: ocaml-libxml2-devel

Requires: maude >= 2.3
Requires(post): /sbin/install-info
Requires(preun): /sbin/install-info

%define _use_internal_dependency_generator 0
%define __find_requires /usr/lib/rpm/ocaml-find-requires.sh
%define __find_provides /usr/lib/rpm/ocaml-find-provides.sh


%description
The creol tools currently provide an emacs mode for writing Creol programs,
a compiler from Creol to the creol interpreter in Maude, and the semantics
in Maude.

%prep
%setup -q

%build
# We have no need to hurry.
%configure OCAMLOPT_FLAGS="-inline 10 -noassert -unsafe"
make %{?_smp_mflags}

# Build the pdf, because most people seem to prefer hard copy stuff.
make pdf

%check
make check

%install
rm -rf $RPM_BUILD_ROOT
export DESTDIR=$RPM_BUILD_ROOT
make install

# If we succeeded in building native versions, we only package this version,
# otherwise we distribute the byte code version.
for i in creolc ; do
    if [ -x $RPM_BUILD_ROOT%{_bindir}/$i.opt ] ; then
        mv $RPM_BUILD_ROOT%{_bindir}/$i.opt $RPM_BUILD_ROOT%{_bindir}/$i
	strip $RPM_BUILD_ROOT%{_bindir}/$i
    fi
done

# install-info dumps a dir file
rm -f $RPM_BUILD_ROOT%{_infodir}/dir

# Now generate the fedora specific configuration.
mkdir -p $RPM_BUILD_ROOT%{_sysconfdir}/profile.d
cat > $RPM_BUILD_ROOT%{_sysconfdir}/profile.d/creol.sh << EOF
test -f %{_sysconfdir}/profile.d/maude.sh && \
  source %{_sysconfdir}/profile.d/maude.sh
MAUDE_LIB=\${MAUDE_LIB:+\${MAUDE_LIB}:}%{_datadir}/%{name}
export MAUDE_LIB
EOF
chmod 0644 $RPM_BUILD_ROOT%{_sysconfdir}/profile.d/creol.sh

%clean
rm -rf $RPM_BUILD_ROOT

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
%{_datadir}/%{name}
%{_infodir}/*.info*
%config(noreplace) %{_sysconfdir}/profile.d/creol.sh

%changelog
* Thu Apr 17 2007 Marcel Kyas <kyas@ifi.uio.no> - 0.0b-0
- Initial build
