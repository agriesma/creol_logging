(*
 * Creol.thy - A deep embedding of Creol in Isabelle.
 *
 * This file is part of creoltools
 *
 * Written and Copyright (c) 2007 by Marcel Kyas
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License as
 * published by the Free Software Foundation; either version 2 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
 * 02111-1307, USA.
 *)

header {* Creol *}

theory Creol
  imports Main
begin

datatype variable = V

datatype name = N

datatype expression = E

datatype statement =
    Skip
  | Release
  | Assert expression
  | Prove expression
  | Assign "variable list" "expression list"
  | Await expression
  | Posit expression
  | AsyncCall variable expression name "expression list"
  | LocalAsyncCall variable name "expression list"
  | LocalSyncCall variable name "expression list"
  | Reply "variable list"
  | Free "variable list"
  | If expression statement statement
  | While expression expression statement
  | Sequence statement statement
  | Choice statement statement
  | Merge statement statement

end
