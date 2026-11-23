module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMoveRight
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0243
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0150
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Formalism.SharpRestriction.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelsOverOfFamily
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0249
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0427
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0071
public import Formalism.LocalToGlobal.Columns.ChainTw
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0296
public import Formalism.LocalToGlobal.GroupLattices.StabilizerCount.StabiliserTrivialOfTiedChain
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThetaLocalEquivalence.ThEquivPStepCIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrimeLocalizationCompanionLatticeEqOfLocalizatio
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat
open Formalism.UG (bc prV)
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.CompanLocP

section General

variable {R : Type*} [CommRing R] {W : Type*} [AddCommGroup W] [Module R W]

theorem mem_locP (p : Ideal R) [p.IsPrime] (M : Submodule R W) (x : W) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ p M ↔ ∃ s ∈ p.primeCompl, s • x ∈ M := Iff.rfl

theorem le_locP (p : Ideal R) [p.IsPrime] (M : Submodule R W) : M ≤ Formalism.HermitianLatticesTheory.localization₂ p M :=
  fun x hx => (mem_locP p M x).2 ⟨1, p.primeCompl.one_mem, by simpa using hx⟩

theorem localization_mono (p : Ideal R) [p.IsPrime] {M M₁ : Submodule R W} (h : M ≤ M₁) :
    Formalism.HermitianLatticesTheory.localization₂ p M ≤ Formalism.HermitianLatticesTheory.localization₂ p M₁ := by
  intro x hx
  obtain ⟨s, hs, hx⟩ := (mem_locP p M x).1 hx
  exact (mem_locP p M₁ x).2 ⟨s, hs, h hx⟩

theorem localization_le_localization_of_le_localization (p : Ideal R) [p.IsPrime] {M M₁ : Submodule R W}
    (h : M ≤ Formalism.HermitianLatticesTheory.localization₂ p M₁) : Formalism.HermitianLatticesTheory.localization₂ p M ≤ Formalism.HermitianLatticesTheory.localization₂ p M₁ := by
  intro x hx
  obtain ⟨s, hs, hx⟩ := (mem_locP p M x).1 hx
  obtain ⟨t, ht, hx'⟩ := (mem_locP p M₁ _).1 (h hx)
  refine (mem_locP p M₁ x).2 ⟨t * s, p.primeCompl.mul_mem ht hs, ?_⟩
  rw [mul_smul]
  exact hx'

end General

section Form

variable {E : Type} [Field E] [NumberField E] {N : ℕ} (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E)

theorem hform_smul_right (x y : Fin N → E) (c : E) :
    Formalism.UG.hform σ J x (c • y) = c * Formalism.UG.hform σ J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_smul_left (x y : Fin N → E) (c : E) :
    Formalism.UG.hform σ J (c • x) y = σ c * Formalism.UG.hform σ J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, map_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_add_left (x x' y : Fin N → E) :
    Formalism.UG.hform σ J (x + x') y = Formalism.UG.hform σ J x y + Formalism.UG.hform σ J x' y := by
  simp only [Formalism.UG.hform, Pi.add_apply, map_add (f := _), ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_zero_left (y : Fin N → E) : Formalism.UG.hform σ J 0 y = 0 := by
  simp [Formalism.UG.hform]

theorem ointSmul (s : 𝓞 E) (y : Fin N → E) : s • y = (s : E) • y :=
  (algebraMap_smul E s y).symm

theorem span_dualSet_le (q : Ideal (𝓞 E)) [q.IsPrime] (Λ Λ' : Submodule (𝓞 E) (Fin N → E)) (hΛ' : Λ'.FG)
    (h' : Λ' ≤ Formalism.HermitianLatticesTheory.localization₂ (q.comap (RingOfIntegers.mapRingHom σ)) Λ) :
    Submodule.span (𝓞 E) (dualSet σ J Λ) ≤
      Formalism.HermitianLatticesTheory.localization₂ q (Submodule.span (𝓞 E) (dualSet σ J Λ')) := by
  classical
  rw [Submodule.span_le]
  intro y hy
  obtain ⟨S, hS⟩ := hΛ'
  have hgen : ∀ g ∈ S, ∃ s ∈ q.primeCompl,
      ((s : 𝓞 E) : E) * Formalism.UG.hform σ J g y ∈ (algebraMap (𝓞 E) E).range := by
    intro g hg
    obtain ⟨t, ht, htg⟩ := (mem_locP _ _ _).1 (h' (hS ▸ Submodule.subset_span hg))
    refine ⟨RingOfIntegers.mapRingHom σ t, ht, ?_⟩
    have e : Formalism.UG.hform σ J (t • g) y = ((RingOfIntegers.mapRingHom σ t : 𝓞 E) : E) * Formalism.UG.hform σ J g y := by
      rw [ointSmul, hform_smul_left]
      rfl
    rw [← e]
    exact hy _ htg
  choose! f hf hf' using hgen
  refine (mem_locP _ _ _).2 ⟨∏ g ∈ S, f g, q.primeCompl.prod_mem (fun g hg => hf g hg), Submodule.subset_span ?_⟩
  intro x hx
  rw [← hS] at hx
  rw [ointSmul, hform_smul_right]
  induction hx using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem f hg
    rw [hc, mul_comm (f g) c, show ((c * f g : 𝓞 E) : E) = (c : E) * (f g : E) from map_mul (algebraMap (𝓞 E) E) c (f g), mul_assoc]
    exact Subring.mul_mem _ ⟨c, rfl⟩ (hf' g hg)
  | zero =>
    rw [hform_zero_left, mul_zero]
    exact Subring.zero_mem _
  | add x x' _ _ hx hx' =>
    rw [hform_add_left, mul_add]
    exact Subring.add_mem _ hx hx'
  | smul c x _ hx =>
    rw [ointSmul, hform_smul_left, mul_left_comm]
    exact Subring.mul_mem _ ⟨RingOfIntegers.mapRingHom σ c, rfl⟩ hx

end Form

theorem locP_companion_le {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E) (q : Ideal (𝓞 E)) [q.IsPrime]
    (Λ Λ' : Submodule (𝓞 E) (Fin N → E)) (hΛ' : Λ'.FG)
    (h : Formalism.HermitianLatticesTheory.localization₂ q Λ = Formalism.HermitianLatticesTheory.localization₂ q Λ')
    (h' : Formalism.HermitianLatticesTheory.localization₂ (q.comap (RingOfIntegers.mapRingHom (sp.cm.sig : E →+* E))) Λ =
      Formalism.HermitianLatticesTheory.localization₂ (q.comap (RingOfIntegers.mapRingHom (sp.cm.sig : E →+* E))) Λ') :
    Formalism.HermitianLatticesTheory.localization₂ q (compan (sp := sp) J a Λ) ≤ Formalism.HermitianLatticesTheory.localization₂ q (compan (sp := sp) J a Λ') := by
  apply localization_le_localization_of_le_localization
  unfold compan
  refine sup_le ((le_locP q Λ).trans (h.le.trans (localization_mono q le_sup_left))) ?_
  refine Submodule.smul_le.2 fun r hr m hm => ?_
  have hd := span_dualSet_le (sp.cm.sig : E →+* E) J q Λ Λ' hΛ' ((le_locP _ Λ').trans h'.symm.le) hm
  obtain ⟨s, hs, hsm⟩ := (mem_locP _ _ _).1 hd
  refine (mem_locP _ _ _).2 ⟨s, hs, ?_⟩
  rw [smul_comm]
  exact Submodule.mem_sup_right (Submodule.smul_mem_smul hr hsm)

theorem locP_companion_eq : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E) (q : Ideal (𝓞 E)) [q.IsPrime]
    (Λ Λ' : Submodule (𝓞 E) (Fin N → E)), Λ.FG → Λ'.FG →
    Formalism.HermitianLatticesTheory.localization₂ q Λ = Formalism.HermitianLatticesTheory.localization₂ q Λ' →
    Formalism.HermitianLatticesTheory.localization₂ (q.comap (RingOfIntegers.mapRingHom (sp.cm.sig : E →+* E))) Λ =
      Formalism.HermitianLatticesTheory.localization₂ (q.comap (RingOfIntegers.mapRingHom (sp.cm.sig : E →+* E))) Λ' →
    Formalism.HermitianLatticesTheory.localization₂ q (compan (sp := sp) J a Λ) = Formalism.HermitianLatticesTheory.localization₂ q (compan (sp := sp) J a Λ') := by
  intro R F E _ _ _ _ _ _ sp N J a q _ Λ Λ' hΛ hΛ' h h'
  exact le_antisymm (locP_companion_le sp J a q Λ Λ' hΛ' h h') (locP_companion_le sp J a q Λ' Λ hΛ h.symm h'.symm)

end GlobalTheory.CompanLocP

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowCharacterIdAddQSmulLatticePreservingEqOneStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowCharacter_id_add_q_smul_latticePreserving_eq_one : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∈ Pr.vGs → ∀ y : HomE X.E (R.N j + cOf R j) (R.N j + cOf R j), (∀ x ∈ lamYat (Pr := Pr) (R := R) j P, y x ∈ lamYat (Pr := Pr) (R := R) j P) → lamRow Ch mu sharp j P (LinearMap.id + (qOf P : X.E) • y) = 1 := by
  first | exact @GlobalTheory.LamRowCong.lamRow_one_add_q | exact GlobalTheory.LamRowCong.lamRow_one_add_q | (intros; apply GlobalTheory.LamRowCong.lamRow_one_add_q <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowFormsCoefficientFieldFormComplexPeriodRows
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.AtG

namespace GlobalTheory.Mem.Col2.KerRat

theorem rowForm_baseChange : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} (I : GlobalTheory.Mem.Col2.TC B X) (h : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι), (∀ s : Finset (Formalism.L2.Col.MtildeV (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps), LinearIndependent B.LL (fun x : s => x.1) → LinearIndependent ℂ (fun x : s => GlobalTheory.Mem.Col2.KerRat.rowForm I l h u a x.1)) ∧ Submodule.span ℂ (Set.range (GlobalTheory.Mem.Col2.KerRat.rowForm I l h u a)) = ⊤ := by
  intro B X I h l u a
  refine ⟨fun s hs => ?_, ?_⟩
  · exact GlobalTheory.Core.Rk.RowRead.rowEmb_linearIndependent (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps (I := I.chIn u a)
      (I.perIn u a).b0 (I.perIn u a).til (I.perIn u a).ext (I.perIn u a).tz (tilOk I h u a).2.2 B.embLL (I.perIn u a).H
      (φ := fun x : s => x.1) hs
  · have key := GlobalTheory.Core.Rk.RowRead.rowEmb_span (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps (I := I.chIn u a)
      (I.perIn u a).b0 (I.perIn u a).til (I.perIn u a).ext (I.perIn u a).tz (tilOk I h u a).2.2 B.embLL
      (GlobalTheory.Mem.FieldsLaws.fields_ok B) (φ := id) (by rw [Set.range_id, Submodule.span_univ])
    exact key

end GlobalTheory.Mem.Col2.KerRat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SeamGLInjective
section
noncomputable section

namespace GlobalTheory.TwU

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG _root_.Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat
open Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G
open scoped TensorProduct

section Seam

variable {D : D7} {X : Fields} (s : Seam D X)

def seamLE {n : ℕ} (g : GL (Fin n) D.host.E) : Sp X.E n ≃ₗ[X.E] Sp X.E n :=
  LinearMap.GeneralLinearGroup.generalLinearEquiv X.E (Fin n → X.E)
    (Matrix.GeneralLinearGroup.toLin (bc (s.iE.symm : D.host.E →+* X.E) g))

theorem seamGL_seamLE {n : ℕ} (g : GL (Fin n) D.host.E) : seamGL s (seamLE s g) = g := by
  ext a b
  simp [seamGL, seamLE, bc]

end Seam

end GlobalTheory.TwU

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardKernelDataWithStandardBaseLevels
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Pdv.stdKer_stdRd : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), I.StdKer l Z t → ∃ t' : KerEntTied ex, I.StdKer l Z t' ∧ GlobalTheory.Pdv.StdRd I l Z t' ∧ t'.TopPinned := by
  intro B X I hOk hP l Z L hT Gi Gl K Y cX ex t hS
  rcases t with ⟨cc, cc_rec, cc_ok, δ, δ_ok, Bb, χ, χ_ok, idl, idl_ok, χ_rec, cD, Xf, seam, seam_ok, Pr, pr_ok, g_rec, Ch, sel, S, word, T_rec, tup, Q_rec, cst, idx, m2, glob, glob_σ, glob_xi, idx_ok, O, rd, rd_chain, O_dgen, O_S, O_lat, O_Th, unf, ent, ent_lam, kf, kf_un, served⟩
  obtain ⟨hX, hseam, hPr, hCh, hsel, hSS, hword, htup, hcst, hidx, hm2, hglob, hamb, hδ, hO⟩ := hS
  dsimp only at hX hseam hPr hCh hsel hSS hword htup hcst hidx hm2 hglob hamb hδ hO
  subst hX
  cases hseam
  cases hPr
  cases hCh
  cases hsel
  subst hSS
  cases htup
  cases hcst
  cases hidx
  subst hm2
  cases hglob
  cases hword
  have hA : ambOf (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) Bb χ cD = I.J.amb B χ := eq_of_heq hamb
  have hm := hOk.hm
  have hpi : ∀ (u : B.Word) (a : I.ι) (w : rowSG (B.primes X) I.sel (I.tup a)), (B.primes X).piT u ∉ w.1.asIdeal := fun u a =>
    (TopStep.tilOk_of_avoid l.pr hOk.sel_ok u ⟨hOk.T_mem u, hOk.g_mem⟩).2.1
  refine ⟨⟨cc, cc_rec, cc_ok, δ, δ_ok, Bb, χ, χ_ok, idl, idl_ok, χ_rec, cD, _, _, seam_ok, _, pr_ok, g_rec, _, _, _, _, T_rec, _, Q_rec, _, _, _, _, glob_σ, glob_xi, idx_ok, O, I.kerRd l Z, fun u a => topChain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (FieldsLaws.fields_ok B) l.pr (hOk.idx_ok a).cst_ok hm (hpi u a) (I.kerRd_top l Z hm u a), O_dgen, O_S, ?_, ?_, unf, ent, ent_lam, kf, kf_un, served⟩, ?_, ?_, ?_⟩
  · exact fun u a i c => (hO.lat u a i c).trans (seamOf_lat B (I.cols l) Z.W Z.V Z.S Z.N Z.G _).symm
  · intro u a i c c'
    rw [hA, AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J χ, χ_rec]
    exact (hO.Th u a i c c').trans (I.kerRd_Th l Z hOk idl_ok hO u a i c c').symm
  · exact ⟨rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, heq_of_eq hA, hδ, hO⟩
  · exact fun u a => ⟨I.kerRd l Z u a, HEq.rfl, fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩
  · exact fun u a => I.kerRd_top l Z hm u a
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StdKerStdRdMark
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Pdv.stdKer_stdRd_mark : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), I.StdKer l Z t → ∃ t' : KerEntTied ex, I.StdKer l Z t' ∧ GlobalTheory.Pdv.StdRd I l Z t' ∧ t'.TopPinned ∧ (∀ (u : B.Word) (a : I.ι) (i : ℕ) (c : ((I.rec7 l Z).chTw u a).cls i), (t'.rd u a).pin i c ↔ (i + 1 ≤ B.R.m ∨ ∃ d, OverRow (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u d ((I.stp u a i).rep c).1.1)) := by
  intro B X I hOk hP l Z L hT Gi Gl K Y cX ex t hS
  rcases t with ⟨cc, cc_rec, cc_ok, δ, δ_ok, Bb, χ, χ_ok, idl, idl_ok, χ_rec, cD, Xf, seam, seam_ok, Pr, pr_ok, g_rec, Ch, sel, S, word, T_rec, tup, Q_rec, cst, idx, m2, glob, glob_σ, glob_xi, idx_ok, O, rd, rd_chain, O_dgen, O_S, O_lat, O_Th, unf, ent, ent_lam, kf, kf_un, served⟩
  obtain ⟨hX, hseam, hPr, hCh, hsel, hSS, hword, htup, hcst, hidx, hm2, hglob, hamb, hδ, hO⟩ := hS
  dsimp only at hX hseam hPr hCh hsel hSS hword htup hcst hidx hm2 hglob hamb hδ hO
  subst hX
  cases hseam
  cases hPr
  cases hCh
  cases hsel
  subst hSS
  cases htup
  cases hcst
  cases hidx
  subst hm2
  cases hglob
  cases hword
  have hA : ambOf (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) Bb χ cD = I.J.amb B χ := eq_of_heq hamb
  have hm := hOk.hm
  have hpi : ∀ (u : B.Word) (a : I.ι) (w : rowSG (B.primes X) I.sel (I.tup a)), (B.primes X).piT u ∉ w.1.asIdeal := fun u a =>
    (TopStep.tilOk_of_avoid l.pr hOk.sel_ok u ⟨hOk.T_mem u, hOk.g_mem⟩).2.1
  refine ⟨⟨cc, cc_rec, cc_ok, δ, δ_ok, Bb, χ, χ_ok, idl, idl_ok, χ_rec, cD, _, _, seam_ok, _, pr_ok, g_rec, _, _, _, _, T_rec, _, Q_rec, _, _, _, _, glob_σ, glob_xi, idx_ok, O, I.kerRd l Z, fun u a => topChain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (FieldsLaws.fields_ok B) l.pr (hOk.idx_ok a).cst_ok hm (hpi u a) (I.kerRd_top l Z hm u a), O_dgen, O_S, ?_, ?_, unf, ent, ent_lam, kf, kf_un, served⟩, ?_, ?_, ?_, ?_⟩
  · exact fun u a i c => (hO.lat u a i c).trans (seamOf_lat B (I.cols l) Z.W Z.V Z.S Z.N Z.G _).symm
  · intro u a i c c'
    rw [hA, AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J χ, χ_rec]
    exact (hO.Th u a i c c').trans (I.kerRd_Th l Z hOk idl_ok hO u a i c c').symm
  · exact ⟨rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, heq_of_eq hA, hδ, hO⟩
  · exact fun u a => ⟨I.kerRd l Z u a, HEq.rfl, fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩
  · exact fun u a => I.kerRd_top l Z hm u a
  · exact fun u a i c => Iff.rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepRepEqOneAtTypePrimes
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Pdv


open Classical in
theorem stepRep_eq_one_at_typePrimes {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (m2 j : ℕ)
    (b : (twSt Ch sel mu cst m2 j).β) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) :
    (twSt Ch sel mu cst m2 j).h b P = 1 := by
  cases j with
  | zero => rfl
  | succ i =>
    by_cases h1 : i + 1 ≤ m2
    · revert b
      rw [show twSt Ch sel mu cst m2 (i+1) = twNext Ch sel mu cst (twSt Ch sel mu cst m2 i) by simp [twSt, h1]]
      intro b
      have hq : P.1 ∉ twQOff (Pr := Pr) sel mu := fun hq => (Finset.mem_sdiff.1 hq).2 hP
      simp only [twNext, hq, dif_neg, not_false_eq_true]
    · by_cases h2 : i + 1 = m2 + 1
      · revert b
        rw [show twSt Ch sel mu cst m2 (i+1) = twUnitSt _ (i+1) by simp [twSt, h1, h2]]
        intro b; rfl
      · revert b
        rw [show twSt Ch sel mu cst m2 (i+1) = twEmptySt _ (i+1) by simp only [twSt, if_neg h1, if_neg h2]]
        intro b; exact b.elim

theorem colNorm_of_tw : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), (∀ a, I.cst a = twCst I.Ch I.sel (I.tup a) I.glob ∧ I.idx a = twIdx I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 2)) → GlobalTheory.Pdv.ColNorm I := by
  intro B X I H a
  obtain ⟨hc, hi⟩ := H a
  refine ⟨?_, ?_, ?_⟩
  · rw [hc]; show B.R.m ≤ B.R.m + 1; omega
  · rw [hc]; show B.R.m ≤ B.R.m; exact le_rfl
  · rw [hi]
    intro j _ b P hP
    exact stepRep_eq_one_at_typePrimes _ _ _ _ _ _ b P hP

end GlobalTheory.Pdv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroTrivialStabilisersTrueColumns
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Pdv.StabZero

open GlobalTheory.Mem.Col2.ClsZero

variable {B : Base} {X : PreX B.toPre} {I : TC B X}

theorem idx_empty (a : I.ι) (u : B.Word) {b : (I.stp u a 0).β} (p : (I.stp u a 0).D b) : p.1.2 = ∅ := by
  obtain ⟨⟨q, Y⟩, hY⟩ := p
  rw [ys0 a] at hY
  exact hY

theorem gam_eq_one (h : I.Ok) (u : B.Word) (a : I.ι)
    (hm : ∀ c' : (I.stp u I.mu0 0).Cl, Nat.card ((I.stp u I.mu0 0).Stab c') = 1)
    (c : (I.stp u a 0).Cl) (s : (I.stp u a 0).Stab c) : s.1.1 = 1 := by
  obtain ⟨b⟩ := stepZero_chartIndex_nonempty h a
  obtain ⟨c', rfl⟩ := (bij0 h u a b).2 c
  have hd := stepZero_corresponding_representatives_same_deco h u a b c'
  set p := (I.stp u a 0).rep (I.cl0 u a b c') with hp
  set p0 := (I.stp u I.mu0 0).rep c' with hp0
  have hs : _ = _ := s.2
  have hsd : ((s.1.1, (s.1.2.1.1 : GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs))) : UF B.fields.E (B.R.N 0) × GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs)) • p.1.1.deco = p.1.1.deco :=
    congrArg (fun x => DecoF.deco x.1.1) hs
  rw [hd] at hsd
  have hγ : ∀ (P : HeightOneSpectrum (𝓞 B.fields.E)) (z : Sp B.fields.E (B.R.N 0)),
      s.1.1.1 z ∈ p0.1.1.deco.1.at P ↔ z ∈ p0.1.1.deco.1.at P := by
    intro P z
    have e := congrArg (fun d : DecoSet (E := B.fields.E) (n := B.R.N 0) (ST := (B.primes X).vT u) (SG := (B.primes X).vGs) => s.1.1.1 z ∈ d.1.at P) hsd
    simp only at e
    rw [← e]
    show s.1.1.1 z ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.HermitianLatticesTheory.gmap s.1.1.1 _) ↔ _
    rw [mem_localization_gmap, LinearEquiv.symm_apply_apply]
  have hc : ∀ P, ((p0.1.1.1.2 P)⁻¹ * (s.1.1.1 * p0.1.1.1.2 P)) ∈ GLint B.fields.E (B.R.N 0) P.1 := by
    intro P x
    show (p0.1.1.1.2 P).symm (s.1.1.1 (p0.1.1.1.2 P x)) ∈ stdAt _ _ P.1 ↔ x ∈ stdAt _ _ P.1
    rw [← p0.1.1.2 P, LinearEquiv.apply_symm_apply, ← p0.1.1.2 P x]
    exact hγ P.1 _
  let t : (I.stp u I.mu0 0).G c'.1 :=
    (s.1.1, ⟨s.1.2.1.1, by
      have e1 := levelTypePrimes_stepZero_eq_colLev h I.mu0 c'.1
      have e2 := levelTypePrimes_stepZero_eq_colLev h a b
      rw [e1, ← e2]
      exact s.1.2.1.2⟩,
     ⟨fun P => ⟨(p0.1.1.1.2 P)⁻¹ * (s.1.1.1 * p0.1.1.1.2 P), hc P⟩, by
      rw [chartIndexLevelTwistPrimes_stepZero_eq_top h I.mu0 c'.1]
      intro P _
      trivial⟩)
  let st : (I.stp u I.mu0 0).Stab c' := ⟨t, by
    show _ = _
    refine Subtype.ext (Prod.ext (Subtype.ext (Prod.ext hsd ?_)) ?_)
    · funext P
      show s.1.1.1 * p0.1.1.1.2 P * (⟨(p0.1.1.1.2 P)⁻¹ * (s.1.1.1 * p0.1.1.1.2 P), hc P⟩⁻¹ : ↥(GLint B.fields.E (B.R.N 0) P.1)).1 = p0.1.1.1.2 P
      simp only [Subgroup.coe_inv]
      group
    · show (fun v => s.1.1.1 v) '' p0.1.2 = p0.1.2
      rw [idx_empty I.mu0 u p0, Set.image_empty]⟩
  have hsub := (Nat.card_eq_one_iff_unique.1 (hm c')).1
  have e : st = 1 := Subsingleton.elim _ _
  exact congrArg (fun x : (I.stp u I.mu0 0).Stab c' => x.1.1) e

theorem card_stab_zero (h : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι)
    (hm : ∀ c' : (I.stp u I.mu0 0).Cl, Nat.card ((I.stp u I.mu0 0).Stab c') = 1) (c : (I.stp u a 0).Cl) :
    Nat.card ((I.stp u a 0).Stab c) = 1 := by
  have e : ∀ s : (I.stp u a 0).Stab c, s = 1 := fun s =>
    Subtype.ext (((l.ch u a).step 0).stab_inj c.1 s.1 _ s.2 (by
      change (ufGL _ _) s.1.1 = 1
      rw [gam_eq_one h u a hm c s, map_one]))
  exact Nat.card_eq_one_iff_unique.2 ⟨⟨fun s s' => (e s).trans (e s').symm⟩, ⟨1⟩⟩

end GlobalTheory.Pdv.StabZero

namespace GlobalTheory.Pdv

open GlobalTheory.Pdv.StabZero

theorem stepZero_trivial_stabilisers_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)),
    LevelData (I.rec7 l Z) → OrbitPlaces.Stab0 (I.rec7 l Z) := by
  intro B X I h _ l Z lev
  exact ⟨Formalism.L2.G.StabilizerCardinality.card_stab0_mem _ lev,
    fun u μ _ c => card_stab_zero h l u μ (fun c' => Formalism.L2.G.StabilizerCardinality.card_stab0_mem _ lev u c') c⟩

end GlobalTheory.Pdv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TransportedLatticesTwoClassesAdmissible
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem adm_seam_lat_rd_pair : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) u μ i j c c', TaylorLogMetric.admitted D _ _ (t.seam.lat ((t.rd u μ).N i c)) (t.seam.lat ((t.rd u μ).N j c')) := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ i j c c'
  rw [← t.O_lat, ← t.O_lat]
  exact ⟨Formalism.L2.Ker.even_rankN _ _, Formalism.L2.Ker.even_rankN _ _, ((t.O u μ).lat i c).2, ((t.O u μ).lat j c').2⟩

end GlobalTheory.TwV
end

