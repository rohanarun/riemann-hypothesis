module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0380
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0377
public import Lean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepLevelContainsDeepCongruenceAtBadPrime
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0104
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ExistsIntegralMulOrderElement
public import Formalism.LocalToGlobal.Columns.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelElementAtBadPrimesIntegralAndNear
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0461
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0443
public import Formalism.LocalToGlobal.Columns.DecoFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0462
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0033
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0319
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0806

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsUnique
section
noncomputable section

namespace GlobalTheory.Mem.SRe.StdUnique

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr
  GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3.Tr

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem pt_of_deco {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} {ST SG Q Q' : Finset (HeightOneSpectrum (𝓞 E))} (hQ : Q' = ∅)
    {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} {p' : DecoF E n ST SG Q'} (e : p'.deco = p.deco)
    (h : IsPtOf hc g p) : IsPtOf hc g p' :=
  ⟨h.uni, e ▸ h.lat, e ▸ h.f, e ▸ h.be, fun P => (Finset.eq_empty_iff_forall_notMem.1 hQ P.1 P.2).elim⟩

variable {B : Base} {X : PreX B.toPre} (I : TC B X)


set_option maxHeartbeats 2000000 in
theorem reads_mem (u : B.Word) (i : ℕ) {Lb Lb' : Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)}
    {U U' : Subgroup (GA B (B.R.N i))} {chi : U →* ℂˣ} {chi' : U' →* ℂˣ} {y : (I.stp u I.mu0 i).Cl → GA B (B.R.N i)}
    {st st' : ∀ c, (I.stp u I.mu0 i).Stab c → GL (Fin (B.R.N i)) B.host.E} {k k' : Unit → GA B (B.R.N i)}
    (hR : I.Reads u I.mu0 i (fun _ => ()) (fun _ => Lb) (fun _ => U) (fun _ => chi) y st k)
    (hR' : I.Reads u I.mu0 i (fun _ => ()) (fun _ => Lb') (fun _ => U') (fun _ => chi') y st' k')
    (x : U) (hx : x.1 ∈ UAd B.sp.cm (B.R.N i)) : ∃ h : x.1 ∈ U', chi' ⟨x.1, h⟩ = chi x := by
  obtain ⟨c, -⟩ := hR.onto ()
  obtain ⟨p0, hp0, -⟩ := hR.k_std ()
  have hk : k () ∈ UAd B.sp.cm (B.R.N i) := hp0.uni
  have hQ : QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K) = ∅ := ColIn.twistPrimes_reference_tuple_eq_empty I
  haveI : NeZero (B.R.N i) := ⟨(B.R.N_pos i).ne'⟩
  have h1 : PtOf (y c * k ()) ((I.stp u I.mu0 i).rep c).1.1 := pt_of_deco hQ (extTo_deco _ _).symm (hR.pt c)
  have h2 : PtOf (y c * k' ()) ((I.stp u I.mu0 i).rep c).1.1 := pt_of_deco hQ (extTo_deco _ _).symm (hR'.pt c)
  have hyk : y c * k () ∈ UAd B.sp.cm (B.R.N i) := h1.uni
  have hg : y c * x.1 * k () ∈ UAd B.sp.cm (B.R.N i) := by
    have e : y c * x.1 * k () = (y c * k ()) * ((k ())⁻¹ * x.1 * k ()) := by group
    rw [e]
    exact mul_mem hyk (mul_mem (mul_mem (inv_mem hk) hx) hk)
  obtain ⟨q, hq⟩ := ChiFinTop.exists_isPtOf_of_mem (ST := (B.primes X).vT u) (SG := (B.primes X).vGs)
    (Q := QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K)) B.sp.cm hQ hg
  have hq' : PtOf (y c * x.1 * k' ()) q := by
    have e : y c * x.1 * k' () = y c * x.1 * k () * ((y c * k ())⁻¹ * (y c * k' ())) := by group
    rw [e]
    exact PtStab.isPtOf_mul_stab _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 hq
  obtain ⟨κ, hgam, hκq, hcos⟩ := (hR.lev c x.1 q hq).1 x.2
  have hm : x.1 ∈ U' := (hR'.lev c x.1 q hq').2 ⟨κ, hgam, hκq, hcos⟩
  refine ⟨hm, Units.ext ?_⟩
  exact (hR'.chr c ⟨x.1, hm⟩ κ hgam (by rw [hκq]; exact hq')).trans (hR.chr c x κ hgam (by rw [hκq]; exact hq)).symm


set_option maxHeartbeats 2000000 in
theorem reads_unique (u : B.Word) (i : ℕ) {Lb Lb' : Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)}
    {U U' : Subgroup (GA B (B.R.N i))} {chi : U →* ℂˣ} {chi' : U' →* ℂˣ} {y y' : (I.stp u I.mu0 i).Cl → GA B (B.R.N i)}
    {st st' : ∀ c, (I.stp u I.mu0 i).Stab c → GL (Fin (B.R.N i)) B.host.E}
    (hR : ∃ k, I.Reads u I.mu0 i (fun _ => ()) (fun _ => Lb) (fun _ => U) (fun _ => chi) y st k)
    (hR' : ∃ k, I.Reads u I.mu0 i (fun _ => ()) (fun _ => Lb') (fun _ => U') (fun _ => chi') y' st' k) (hy : y' = y)
    (hU : U ≤ UAd B.sp.cm (B.R.N i)) (hU' : U' ≤ UAd B.sp.cm (B.R.N i)) : Lb' = Lb ∧ U' = U ∧ HEq chi' chi := by
  obtain ⟨k, hR⟩ := hR
  obtain ⟨k', hR'⟩ := hR'
  subst hy
  have e : U' = U := le_antisymm (fun x hx => (reads_mem I u i hR' hR ⟨x, hx⟩ (hU' hx)).1)
    fun x hx => (reads_mem I u i hR hR' ⟨x, hx⟩ (hU hx)).1
  subst e
  refine ⟨Submodule.ext fun x => (hR'.lb () x).trans (hR.lb () x).symm, rfl, heq_of_eq (MonoidHom.ext fun x => ?_)⟩
  exact (reads_mem I u i hR hR' x (hU x.2)).2

variable (l : I.Laws)


set_option maxHeartbeats 2000000 in
theorem lev_le (hI : I.Ok) (hP : TC.Pins B X) (Z : TC.Later B (I.cols l)) (u : B.Word) (i : ℕ) (hi : i ≤ B.R.m)
    (K : ClsTied (D := I.rec7 l Z) u i hi) : (show Subgroup (GA B (B.R.N i)) from K.lev.U) ≤ UAd B.sp.cm (B.R.N i) := by
  have hg1 : gramN (I.rec7 l Z) i hi = 1 := ((spaces_in_coordinates I hI hP l Z).2.2.2 i hi).1
  have eU : UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) =
      UAd B.sp.cm (B.R.N i) := by rw [hg1]; rfl
  exact fun x hx => eU ▸ ((K.lev.U_eq x).1 hx).1


set_option maxHeartbeats 4000000 in
theorem std_pair (hI : I.Ok) (hP : TC.Pins B X) (Z Z' : TC.Later B (I.cols l)) (u : B.Word) {Ch Ch' : ℕ → Type}
    {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} {chOf' : ∀ i, ((I.rec7 l Z').mem u).C.cls i → Ch' i}
    (F : FormsTiedSym (I.rec7 l Z) u Ch chOf) (F' : FormsTiedSym (I.rec7 l Z') u Ch' chOf')
    (hF : I.StdF l Z u F) (hF' : I.StdF l Z' u F') :
    F'.to0.cls0.lev.Lb = F.to0.cls0.lev.Lb ∧ F'.to0.cls0.lev.U = F.to0.cls0.lev.U ∧ HEq F'.to0.cls0.lev.chi F.to0.cls0.lev.chi ∧
      F'.to0.cls0.y = F.to0.cls0.y ∧ F'.to0.val0.eY = F.to0.val0.eY := by
  have hy : ∀ c : (I.stp u I.mu0 0).Cl, (F'.to0.cls0.y c).1 = (F.to0.cls0.y c).1 := fun c =>
    (hF'.yE 0 (Nat.zero_le _) (Or.inl rfl) c).trans (hF.yE 0 (Nat.zero_le _) (Or.inl rfl) c).symm
  have h := reads_unique I u 0 (hF.ends 0 (Nat.zero_le _) (Or.inl rfl)) (hF'.ends 0 (Nat.zero_le _) (Or.inl rfl)) (funext hy)
    (lev_le I l hI hP Z u 0 _ _) (lev_le I l hI hP Z' u 0 _ _)
  refine ⟨h.1, h.2.1, h.2.2, funext fun c => Subtype.ext (hy c), Equiv.ext fun z => Subtype.ext ?_⟩
  exact (hF'.eY 0 (Nat.zero_le _) (Or.inl rfl) z).trans (hF.eY 0 (Nat.zero_le _) (Or.inl rfl) z).symm


set_option maxHeartbeats 4000000 in
theorem car_of_same {D : D7} {u : D.what₂.Word} {F₁ F' : Forms0 D u}
    {lev : StepLevel D.host.F D.host.E (sigD D) (gramN D 0 (Nat.zero_le _)) (D.mem u).A.T D.R.f (badG D)}
    {y : (D.mem u).C.cls 0 → UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)}
    {eY : (D.mem u).C.Y 0 ≃ Formalism.L2.Forms.Fr D 0 (Nat.zero_le _)}
    (h : F₁.cls0.lev = lev ∧ F₁.cls0.y = y ∧ F₁.val0.eY = eY)
    (h' : F'.cls0.lev.Lb = lev.Lb ∧ F'.cls0.lev.U = lev.U ∧ HEq F'.cls0.lev.chi lev.chi ∧ F'.cls0.y = y ∧ F'.val0.eY = eY) :
    F'.cls0.lev.Lb = F₁.cls0.lev.Lb ∧ F'.cls0.lev.U = F₁.cls0.lev.U ∧ HEq F'.cls0.lev.chi F₁.cls0.lev.chi ∧
      F'.cls0.y = F₁.cls0.y ∧ F'.val0.eY = F₁.val0.eY := by
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact h'


set_option maxHeartbeats 4000000 in
theorem sameStd : SameStd := by
  intro B f T w Z Zn col col' F₁ h u
  have h1 := std_pair w.I w.l w.ok w.pins Z (reL Z Zn) u (col.C.forms u) (col'.C.forms u) (col.std u) (col'.std u)
  exact car_of_same (F₁ := F₁ u) (F' := (col'.C.forms u).to0) (lev := (by with_unfolding_all exact ((col.C.forms u).to0.cls0.lev :)))
    (y := (by with_unfolding_all exact ((col.C.forms u).to0.cls0.y :))) (eY := (by with_unfolding_all exact ((col.C.forms u).to0.val0.eY :))) ((by with_unfolding_all exact ((h u) :))) ((by with_unfolding_all exact (h1 :)))

end GlobalTheory.Mem.SRe.StdUnique

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RepresentativeImagePointOfLift
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.LevLiftPt

theorem isPtOf_mul_fr {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    {hc : CMData F E} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))} {g m : GL (Fin n) (AfE F E)}
    {p : DecoF E n ST SG Q} (hg : IsPtOf hc g p)
    (hm : m ∈ Formalism.L2.Herm.UstdAf hc n) (h1 : ∀ i j, (m : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ RInt F E)
    (h2 : ∀ i j, ((m⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ RInt F E)
    (hT : ∀ P ∈ ST, ∀ i j, adAt F P ((m : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
      adAt F P (((1 : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j))
    {h : GLG (E := E) (n := n) (SG := SG)} (hh : ∀ w : SG, LevRead.IsRed w.1 m (h w)) (c : GLQ E n Q)
    (hfr : ∀ (P : Q) (i j : Fin n), adAt F P.1 (((g * m⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
      algebraMap E _ ((p.fr P * ((c P)⁻¹ : GLint E n P.1).1) (Pi.single j 1) i)) :
    IsPtOf hc (g * m⁻¹) (((1, h, c) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p) := by
  have hg0 : IsPtOf hc g (ChTwRead.noFr p) :=
    ⟨hg.uni, hg.lat, hg.f, hg.be, fun P => absurd P.2 (Finset.notMem_empty _)⟩
  have H := LevRead.isPtOf_mul (Q := ∅) (fun P => Finset.notMem_empty P) hg0 hm h1 h2 hT hh
    (fun P => absurd P.2 (Finset.notMem_empty _))
  refine ⟨H.uni, H.lat, H.f, H.be, fun P i j => ?_⟩
  rw [hfr P i j]
  rfl

theorem int_of_split : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : CMData F E) {n : ℕ} (u : GL (Fin n) (AfE F E)), u ∈ Formalism.L2.Herm.UstdAf hc n → ∀ (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)), Formalism.L2.Col.IsOver v P → (∀ v', v' ≠ v → bc (prV (E := E) v') u = 1) → ∀ g ∈ Formalism.L2.Col.GLint E n P, (∀ r s, adAt F P ((u : Matrix (Fin n) (Fin n) (AfE F E)) r s) = algebraMap E (P.adicCompletion E) (LinearMap.toMatrix' g.toLinearMap r s)) → ∀ i j, (u : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ RInt F E ∧ ((u⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ RInt F E :=
  GlobalTheory.T.supported_unitary_adelic_integral_with_inverse

theorem vT_notOver : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (a : I.ι) (P : SBof I a) (v : HeightOneSpectrum (𝓞 B.host.F)), Formalism.L2.Col.IsOver v P.1 → ∀ (u : B.Word), ∀ P' ∈ (B.primes X).vT u, ¬ Formalism.L2.Col.IsOver v P' :=
  _root_.GlobalTheory.Mem.Col2.AdT.vT_notOver_SBof

theorem isRed_of_red : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E)), ∀ g ∈ Formalism.L2.Col.GLint E n P, ∀ (A : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)), (∀ y ∈ Formalism.L2.Col.stdAt E n P, redV P (g y) = A.mulVec (redV P y)) → ∀ (m : GL (Fin n) (AfE F E)), (∀ r s, adAt F P ((m : Matrix (Fin n) (Fin n) (AfE F E)) r s) = algebraMap E (P.adicCompletion E) (LinearMap.toMatrix' g.toLinearMap r s)) → LevRead.IsRed P m A := by
  intro F E _ _ _ _ _ _ n P g hg A hA m hm r s
  have h := ReadBad.isRed_ratA (F := F) hg hA r s
  have e : adAt F P (((GlobalTheory.TwU.ratA F (toGLm E n g) : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) r s) =
      algebraMap E (P.adicCompletion E) (LinearMap.toMatrix' g.toLinearMap r s) := by
    show adAt F P (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) _) = _
    rw [adAt_inclE]
    rfl
  show HasRes P _ _
  rw [hm r s, ← e]
  exact h

theorem adAt_of_off {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] {n : ℕ}
    {u : GL (Fin n) (AfE F E)} {v : HeightOneSpectrum (𝓞 F)} (hoff : ∀ v', v' ≠ v → bc (prV (E := E) v') u = 1)
    {Q : HeightOneSpectrum (𝓞 E)} (hQ : ¬ Formalism.L2.Col.IsOver v Q) (i j : Fin n) :
    adAt F Q ((u : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
      adAt F Q (((1 : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j) := by
  have hne : Q.under (𝓞 F) ≠ v := by
    rintro rfl
    exact hQ rfl
  refine ChTwRead.adAt_congr_prV Q ?_
  have h1 := congrArg (fun g : GL (Fin n) (E ⊗[F] (Q.under (𝓞 F)).adicCompletion F) => g.val i j) (hoff _ hne)
  have h2 := congrArg (fun g : GL (Fin n) (E ⊗[F] (Q.under (𝓞 F)).adicCompletion F) => g.val i j)
    (map_one (bc (prV (E := E) (Q.under (𝓞 F)))) : bc (prV (E := E) (Q.under (𝓞 F))) (1 : GL (Fin n) (AfE F E)) = 1)
  exact h1.trans h2.symm

theorem core {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (hc : CMData F E) {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))} {g0 x kk : GL (Fin n) (AfE F E)}
    {p : DecoF E n ST SG Q} (hp : IsPtOf hc g0 p) (hx : x ∈ Formalism.L2.Herm.UstdAf hc n) (hk : kk ∈ Formalism.L2.Herm.UstdAf hc n)
    (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)) (hv : Formalism.L2.Col.IsOver v P)
    (hxoff : ∀ v', v' ≠ v → bc (prV (E := E) v') x = 1) (g' : Sp E n ≃ₗ[E] Sp E n) (hg' : g' ∈ Formalism.L2.Col.GLint E n P)
    (hpt : ∀ r s, adAt F P (((kk⁻¹ * x * kk : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) r s) =
      algebraMap E (P.adicCompletion E) (LinearMap.toMatrix' g'.toLinearMap r s))
    (hST : ∀ P' ∈ ST, ¬ Formalism.L2.Col.IsOver v P') (hover : ∀ w, w ∈ SG ∨ w ∈ Q → Formalism.L2.Col.IsOver v w → w = P)
    (h : GLG (E := E) (n := n) (SG := SG)) (c : GLQ E n Q)
    (hG : ∀ hP : P ∈ SG, ∀ y ∈ Formalism.L2.Col.stdAt E n P, redV P (g' y) = ((h ⟨P, hP⟩)⁻¹).1.mulVec (redV P y))
    (hGo : ∀ w : SG, w.1 ≠ P → ∀ y ∈ Formalism.L2.Col.stdAt E n w.1,
      redV w.1 ((1 : Sp E n ≃ₗ[E] Sp E n) y) = ((h w)⁻¹).1.mulVec (redV w.1 y))
    (hQ : ∀ hP : P ∈ Q, g' = ((c ⟨P, hP⟩)⁻¹).1)
    (hQo : ∀ P'' : Q, P''.1 ≠ P → (1 : Sp E n ≃ₗ[E] Sp E n) = ((c P'')⁻¹).1) :
    IsPtOf hc (g0 * (kk⁻¹ * x * kk)) (((1, h, c) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p) := by
  set m := kk⁻¹ * x * kk with hm
  have hmU : m ∈ Formalism.L2.Herm.UstdAf hc n := mul_mem (mul_mem (inv_mem hk) hx) hk
  have hmoff : ∀ v', v' ≠ v → bc (prV (E := E) v') m = 1 := fun v' hv' => by
    rw [hm, map_mul, map_mul, map_inv, hxoff v' hv', mul_one, inv_mul_cancel]
  have hmioff : ∀ v', v' ≠ v → bc (prV (E := E) v') m⁻¹ = 1 := fun v' hv' => by
    rw [map_inv, hmoff v' hv', inv_one]
  have hInt := int_of_split hc m hmU v P hv hmoff g' hg' hpt
  have e : g0 * m = g0 * m⁻¹⁻¹ := by rw [inv_inv]
  rw [e]
  refine isPtOf_mul_fr hp (inv_mem hmU) (fun r s => (hInt r s).2) (fun r s => by rw [inv_inv]; exact (hInt r s).1) ?_ ?_ c ?_
  · intro P' hP' r s
    exact adAt_of_off hmioff (hST P' hP') r s
  · intro w
    by_cases hw : w.1 = P
    · obtain ⟨w, hwm⟩ := w
      simp only at hw
      subst hw
      have hC := isRed_of_red w g' hg' _ (hG hwm) m hpt
      obtain ⟨Bm, hB⟩ := LevRead.exists_isRed (x := m⁻¹) (P := w)
        (fun r s => (mem_rInt_iff F E _).1 (hInt r s).2 w)
        (fun r s => by rw [inv_inv]; exact (mem_rInt_iff F E _).1 (hInt r s).1 w)
      have h1 := hC.mul hB
      rw [mul_inv_cancel] at h1
      have h2 := h1.unique LevRead.isRed_one
      have h3 : (h ⟨w, hwm⟩)⁻¹ * Bm = 1 := Units.ext (by rw [Units.val_mul]; exact h2)
      rw [inv_mul_eq_one] at h3
      rw [h3]
      exact hB
    · have hwnot : ¬ Formalism.L2.Col.IsOver v w.1 := fun h' => hw (hover w.1 (Or.inl w.2) h')
      have hC1 := isRed_of_red (F := F) w.1 1 (one_mem _) _ (hGo w hw) (1 : GL (Fin n) (AfE F E)) (fun r s => by
        rw [show LinearMap.toMatrix' (1 : Sp E n ≃ₗ[E] Sp E n).toLinearMap = 1 from LinearMap.toMatrix'_id]
        simp only [Units.val_one, Matrix.one_apply]
        split_ifs <;> simp)
      have h2 := hC1.unique LevRead.isRed_one
      have h3 : (h w)⁻¹ = 1 := Units.ext h2
      rw [inv_eq_one] at h3
      rw [h3]
      intro r s
      rw [adAt_of_off hmioff hwnot r s]
      exact LevRead.isRed_one r s
  · intro P'' r s
    set_option synthInstance.maxHeartbeats 100000 in
      rw [inv_inv, Units.val_mul, Matrix.mul_apply, map_sum]
    by_cases hPP : P''.1 = P
    · obtain ⟨P'', hPm⟩ := P''
      simp only at hPP
      subst hPP
      rw [← hQ hPm]
      simp_rw [map_mul, hp.fr ⟨P'', hPm⟩ r, hpt, ← map_mul]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum]
      congr 1
      rw [LinearEquiv.mul_apply]
      set_option synthInstance.maxHeartbeats 100000 in
        conv_rhs => rw [pi_eq_sum_univ (g' (Pi.single s 1)), map_sum]
      simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, LinearMap.toMatrix'_apply,
        LinearEquiv.coe_coe]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [mul_comm]
      congr 2
      exact congrArg (fun y => p.fr ⟨P'', hPm⟩ y r) (by funext j; simp [Pi.single_apply, eq_comm])
    · have hPnot : ¬ Formalism.L2.Col.IsOver v P''.1 := fun h' => hPP (hover P''.1 (Or.inr P''.2) h')
      rw [← hQo P'' hPP, mul_one]
      simp_rw [map_mul, adAt_of_off hmoff hPnot]
      simp only [Units.val_one, Matrix.one_apply, apply_ite (adAt F P''.1), map_one, map_zero, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact hp.fr P'' r s

theorem mul_conj {G : Type} [Group G] (y x k : G) : y * k * (k⁻¹ * x * k) = y * x * k := by group


set_option maxHeartbeats 1000000 in
theorem pt_of_lift : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ (c : (I.stp u a i).Cl) (kk : GL (Fin ((I.rec7 l Z).R.N i)) (TensorProduct (I.rec7 l Z).host.F (I.rec7 l Z).host.E (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F))), kk = k (chOf c) → ∀ (P : SBof I a) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∀ x ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), (∀ v', v' ≠ v → bc (prV (E := (I.rec7 l Z).host.E) v') x = 1) → ∀ g' ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1, (∀ r s, adAt (I.rec7 l Z).host.F (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((kk⁻¹ * x * kk).1 r s) = algebraMap (I.rec7 l Z).host.E ((GlobalTheory.TwU.seamP (sm I l Z) P.1).adicCompletion (I.rec7 l Z).host.E) ((GlobalTheory.TwU.seamGL (sm I l Z) g').1 r s)) → ∀ κ' : (I.stp u a i).G c.1, Keeps I κ' ((I.stp u a i).rep c) → LiftsInv I κ' P g' → (∀ P', P' ≠ P → LiftsInv I κ' P' 1) → PtOf (((K (chOf c)).y ⟨c, rfl⟩).1 * x * kk) (((I.stp u a i).act c.1 κ' ((I.stp u a i).rep c)).1.1) := by
  intro B X I hOk hPins l Z u a i hi bad Ch chOf K k hR c kk hkk P v hv x hx hxoff g' hg' hpt κ' hK hLP hLo
  have hseam : GlobalTheory.TwU.seamP (sm I l Z) P.1 = P.1 := by
    ext y
    exact GlobalTheory.TwU.mem_seamP (sm I l Z) P.1 y
  rw [hseam] at hv hpt
  obtain ⟨hLev, hdisj, -⟩ := GlobalTheory.Mem.LevTwist.levOk_twists B X I hOk
  have hd : Disjoint (B.primes X).vGs (I.Q a) := Finset.disjoint_of_subset_right (ColIn.Q_subset_SQ I a) hdisj
  have hp := IsPtOf.of_extTo (ColIn.Q_subset_SQ I a) hd (hR.pt c)
  rw [← hkk] at hp

  obtain ⟨pk, hpk, -⟩ := hR.k_std (chOf c)
  have hk : kk ∈ UAd B.sp.cm (B.R.N i) := hkk ▸ hpk.uni
  have hg1 : gramN (I.rec7 l Z) i hi = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hOk hPins l Z).2.2.2 i hi).1
  have hxU : x ∈ UAd B.sp.cm (B.R.N i) := by
    have e : UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) =
        UAd B.sp.cm (B.R.N i) := by rw [hg1]; rfl
    exact e ▸ hx
  have hγ : κ'.1 = 1 := by
    have h1 : toGLm B.fields.E (B.R.N i) κ'.1.1 = toGLm B.fields.E (B.R.N i) 1 := by
      rw [map_one]
      exact hK.1
    exact Subtype.ext ((toGLm B.fields.E (B.R.N i)).injective h1)
  have hq : ((I.stp u a i).act c.1 κ' ((I.stp u a i).rep c)).1.1 =
      ((1, fun w => (κ'.2.1.1 w), κ'.2.2.1) : UF B.fields.E (B.R.N i) × GLG (E := B.fields.E) (n := B.R.N i) (SG := (B.primes X).vGs) × GLQ B.fields.E (B.R.N i) (I.Q a)) • ((I.stp u a i).rep c).1.1 := by
    show FrmG.incl _ _ κ' • _ = _
    rw [← hγ]
    rfl

  have hPu : P.1 ∈ uSG (B.primes X).vGs I.SQ := by
    have h := P.2
    simp only [uSG, Finset.mem_union] at h ⊢
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (ColIn.Q_subset_SQ I a h)
  have hS : ∀ w, w ∈ (B.primes X).vGs ∨ w ∈ I.Q a → w ∈ SBof I a := by
    intro w hw
    show w ∈ uSG _ _
    simp only [uSG, Finset.mem_union]
    exact hw
  have key := core B.sp.cm hp hxU hk v P.1 hv hxoff g' hg' hpt (vT_notOver I hOk a P v hv u) (fun w hw hwv => by
      have hw' : w ∈ uSG (B.primes X).vGs I.SQ := by
        simp only [uSG, Finset.mem_union]
        rcases hw with h | h
        · exact Or.inl h
        · exact Or.inr (ColIn.Q_subset_SQ I a h)
      rcases rll_over_cases B.sp.cm hv hwv with h | h
      · exact h
      · exact absurd (h ▸ hw') (hLev.split P.1 hPu))
    (fun w => κ'.2.1.1 w) κ'.2.2.1 hLP.2.1
    (fun w hw => (hLo ⟨w.1, hS w.1 (Or.inl w.2)⟩ (fun e => hw (congrArg Subtype.val e))).2.1 w.2)
    hLP.2.2
    (fun P'' hP'' => (hLo ⟨P''.1, hS P''.1 (Or.inr P''.2)⟩ (fun e => hP'' (congrArg Subtype.val e))).2.2 P''.2)
  have e := mul_conj (G := GA B (B.R.N i)) ((K (chOf c)).y ⟨c, rfl⟩).1 x kk
  rw [hq]
  exact e ▸ key

end GlobalTheory.Mem.Col2.LevLiftPt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowIdentificationsRealRowSideOfChainComparisonStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowIdentifications_realRowSide_of_chainComparison : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (y : Hd R), Inputs D → R.BaseW F → (∀ μ, Used0 D μ ↔ y.Us μ) → ∀ (b : Bool) (rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r) (EE : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (S : RowSide D EE) (n : ℕ) (bs : OrthonormalBasis (Fin n) ℂ EE) (ty : Fin n → D.what₂.FT) (jA : ∀ t, (Fin (rDim D A (levP F b).1 (levP F b).2 t) → D.what₂.LL) → S.Amb (y.tup t)) (t : ChT y F b rep (Top := fun μ => ⟨S.Amb μ⟩) jA ⟨⟨EE⟩, fun μ j => ⟨S.Mult μ j⟩, S.multZero, S.multTop, S.io, n, bs, ty⟩), ∃ I : RowIds S (y.C F) b, RowSideReal S (y.C F) b I bs ty ∧ (∀ π, I.prt π = y.prtE F b (rep π)) ∧ (∀ x, (I.jE x).1 = t.jE x) ∧ ∀ μ h x, (I.jX μ h x).1 = t.jX μ (S.multTop μ x) := by
  first | exact @GlobalTheory.Mem.R3.Rw.rowSide_of_chainTie | exact GlobalTheory.Mem.R3.Rw.rowSide_of_chainTie | (intros; apply GlobalTheory.Mem.R3.Rw.rowSide_of_chainTie <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowsAre
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}

def St.rowsAre {P : Pre2 K w} (x : St P) (hη : ∀ j v, 1 ≤ j → j ≤ B.R.m → x.o.η j v = P.q.eta j v) :
    R3.RowsAre (w.st x.o.Z) w.I P.hX T P.Wt (Equiv.refl _) x.s.p0 :=
  ⟨x.m.z, x.m.intersectionNumber_baseChange, x.r.Y, x.r.Z.full fun j v h1 h2 => (x.m.eta j v).symm ▸ hη j v h1 h2, fun t => by
    change x.r.Y.tup t = _
    rw [x.r.tup]; exact x.m.tup t⟩

end GlobalTheory.Mem.R3.Rw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpectralComparisonTransportedDivisionLatticeChan
section
noncomputable section

open GlobalTheory.Mem.R3.Tr Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists Formalism.MainNotions Formalism.L2.Forms Formalism.L2.SG.PackageTie2 MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe GlobalTheory.Mem.Top.Bl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SRe

theorem of_heq_cast {α β : Sort _} {y : β} {x : α} (P : α → Prop) (h : HEq y x) (hx : P x) :
    P (cast (type_eq_of_heq h) y) := by
  cases h
  exact hx


set_option maxHeartbeats 4000000 in
theorem sAtL_exists_ofDiv : ∀ (B : Base) (C : Cols B) (a : Late B C) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn a.D.what₂.LL G' Pl0 T a.D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks a.D.what₂.LL] (R : RealDat a.D A Ks) (F : Face a.D A) (F0 : ∀ u, Forms0 a.D u) (eE : a.D.what₂.EE →ₗ[ℂ] R.HE.H) (s : SAt R F eE F0) (N : ∀ u, Submodule (𝓞 a.D.what₂.LL) (a.D.div.Nu u).V) (hh : a.D.what₂.Word → ℝ) (F₁ : ∀ u, Forms0 (reL a (New.ofDiv a.D N hh)).D u), SameL a (New.ofDiv a.D N hh) F0 F₁ → ∃ s' : SAtL a (New.ofDiv a.D N hh) R F eE F₁, SAtL.pt a (New.ofDiv a.D N hh) s' = tL a (New.ofDiv a.D N hh) s.t := by
  intro B C a G' _ _ Pl0 T A Ks _ _ iK R F F0 eE s N hh F₁ hS
  have hF : FinX (reY (New.ofDiv a.D N hh) s.P.Y) := finX_reY a.D (New.ofDiv a.D N hh) s.P.X s.P.Y s.P.fin
  have h : SameForms0LevelsAndValues (New.ofDiv a.D N hh) F0 ((by with_unfolding_all exact (F₁ :))) := hS
  obtain ⟨S', hj⟩ := SRest.exists_re_ofDiv N hh s.S h hF
  have hsee := mvSee a (New.ofDiv a.D N hh) R F s.P.X s.P.inst s.t s.see
  have hev := mvEv_holds a (New.ofDiv a.D N hh) R F s.P.X s.P.inst s.P.G s.t s.c s.ev
  have hrow := mvRowJ a (New.ofDiv a.D N hh) R s.P.X s.P.inst s.P.G s.t eE s.S.j s.rowJ
  letI := alg (reL a (New.ofDiv a.D N hh)) iK
  have hrow' := of_heq_cast (fun j : a.D.what₂.EE ≃ₗᵢ[ℂ] EEC s.P.X s.P.G =>
      RowJ (real (reL a (New.ofDiv a.D N hh)) R) (eL a (New.ofDiv a.D N hh) R eE) (XL a (New.ofDiv a.D N hh) s.P.X)
        (hL a (New.ofDiv a.D N hh) s.P.inst) (gdL a (New.ofDiv a.D N hh) s.P.G) (tL a (New.ofDiv a.D N hh) s.t)
        (jL a (New.ofDiv a.D N hh) j)) hj hrow
  let s' : SAt (real (reL a (New.ofDiv a.D N hh)) R) (face (reL a (New.ofDiv a.D N hh)) F) (eL a (New.ofDiv a.D N hh) R eE) F₁ :=
    { P := (by with_unfolding_all exact (s.P.re (New.ofDiv a.D N hh) h hF :))
      S := (by with_unfolding_all exact (S' :))
      t := tL a (New.ofDiv a.D N hh) s.t
      c := s.c
      c_pos := s.c_pos
      see := (by with_unfolding_all exact (hsee :))
      ev := (by with_unfolding_all exact (hev :))
      rowJ := (by with_unfolding_all exact (hrow' :)) }
  exact ⟨s', (by with_unfolding_all exact (Eq.refl (tL a (New.ofDiv a.D N hh) s.t) :))⟩

end GlobalTheory.Mem.SRe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SwapCastEqSwapAE
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MtId

variable {D : D7}

theorem idFrame_iff_unitFr {V : HSp D} (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V V.rank) :
    GlobalTheory.MtRead.IdFrame hF P ↔ GlobalTheory.MtIn.UnitFr P := by
  constructor
  · rintro ⟨hn, h⟩ κ
    refine Units.ext (Matrix.ext fun a b => ?_)
    have := (RingEquiv.eq_symm_apply _).1 (h κ a b)
    exact this
  · intro h
    refine ⟨rfl, fun κ a b => (RingEquiv.eq_symm_apply _).2 ?_⟩
    exact congrArg (fun g : GL (Fin V.rank) (EAf D) => g.val a b) (h κ)

def castFr {V : HSp D} {n : ℕ} (hn : V.rank = n) (P : principalLevelFrame.RowPsi V V.rank) : principalLevelFrame.RowPsi V n := hn ▸ P

theorem idFrame_castFr {V : HSp D} {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (hn : V.rank = n)
    {P : principalLevelFrame.RowPsi V V.rank} (h : GlobalTheory.MtIn.UnitFr P) : GlobalTheory.MtRead.IdFrame hF (castFr hn P) := by
  subst hn
  exact (idFrame_iff_unitFr hF P).2 h

end GlobalTheory.MtId

end
end

