module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousNormFin

@[expose] public section

noncomputable section

namespace GlobalTheory.HeightCounting.Up.RowModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting
  GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

theorem overRows_allSt {p : RowP} (h : OverRows p) :
    AllSt fun K B f T w P x => p K B f T w x.o.Z P.Wt P.hX x.m.z x.s.p0 x.r.Y :=
  EvG.imp h fun _ _ _ _ _ hK => large₂.imp hK fun _ _ _ _ H kp _ _ w s P x =>
    s.1.elim fun c => H kp w c x.o.Z P.Wt P.hX x.m.z x.s.p0 x.r.Y x.m.intersectionNumber_baseChange x.m.exAt x.m.inGeo x.fits.grp x.fits.grpAt


end GlobalTheory.HeightCounting.Up.RowModel

end
