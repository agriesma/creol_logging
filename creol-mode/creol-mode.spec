Name:		creol-mode
Version:	0.0a
Release:	0%{?dist}
Summary:	Emacs editing mode for Maude
Source:		creol-mode-%version.tar.bz2
Source1:	creol-mode-init.el
License:	GPL
Group:		Development/Other
BuildRequires:	emacs
Requires:	emacs
URL:		http://heim.ifi.uio.no/~kyas/creoltools
Packager:       Marcel Kyas <kyas@ifi.uio.no>
BuildRoot:	%{_tmppath}/%{name}-%{version}-%{release}-root-%(%{__id_u} -n)
BuildArch:	noarch
Requires:	creoltools

%description
Maude mode is an editing mode for emacs.

%package el
Group:		Development/Other
Summary:	The emacs lisp source files of creol-mode
Requires:	%name = %version-%release

%description el
The emacs lisp source files of creol-mode.

%prep
rm -rf $RPM_BUILD_ROOT
%setup -q -T -b 0
%configure

%build
make

%install
make DESTDIR=$RPM_BUILD_ROOT install
mkdir -p $RPM_BUILD_ROOT%{_datadir}/emacs/site-lisp/site-start.d
install -m0644 %SOURCE1 $RPM_BUILD_ROOT%{_datadir}/emacs/site-lisp/site-start.d

%clean
rm -rf $RPM_BUILD_ROOT

%files
%defattr(-,root,root)
%doc README NEWS COPYING
%{_datadir}/emacs/site-lisp/creol-mode.elc
%{_datadir}/emacs/site-lisp/site-start.d/creol-mode-init.el

%files el
%{_datadir}/emacs/site-lisp/creol-mode.el

%changelog
* Mon Jun 20 2007 Marcel Kyas <kyas@ifi.uio.no> 0.0-0
- Initial version
