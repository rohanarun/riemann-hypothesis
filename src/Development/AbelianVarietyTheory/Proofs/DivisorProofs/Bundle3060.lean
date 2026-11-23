module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2823
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2742
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2956
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2767
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2771
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2775
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2043
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2558
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2449
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2644
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2669
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2949
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2637
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2666
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1084
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2752
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2696

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyDieudonneIntegralityFactorisation
section
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

open _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu.AbVarDieu

variable {p : ℕ} [Fact p.Prime]

theorem pow_comp_hom {S : Scheme.{0}} {Z G H : Over S} [GrpObj G] [GrpObj H] (φ : G ⟶ H) [IsMonHom φ]
    (x : Z ⟶ G) (n : ℕ) : (x ^ n) ≫ φ = (x ≫ φ) ^ n := by
  induction n with
  | zero => simp [pow_zero, MonObj.one_comp]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]

theorem exists_eq_ppow_smul (T : Theory p) {k : Type} [Field k] [CharP k p] [PerfectRing k p]
    {A B : AbVar k} {G H : PDivGroup p k} (t : G.TorsionTower A.X) (t' : H.TorsionTower B.X) (f : A ⟶ B)
    (n : ℕ) (h : ∀ m, ∃ m', T.map (t.map t' f.hom) m = p ^ n • m') : ∃ f' : A ⟶ B, f = p ^ n • f' := by
  obtain ⟨g, hg⟩ := (_root_.GlobalTheory.Dieu.Integrality.exists_pow_smul_and_faithful p T k G H (t.map t' f.hom)).1 n h
  exact (GlobalTheory.T.eq_pow_smul_of_pDivGroup_torsionTower_map p k A B G H t t' f).1 n g hg

theorem map_nsmul_id {k : Type} [Field k] {A : AbVar k} {G : PDivGroup p k} (t : G.TorsionTower A.X) (N : ℕ) :
    t.map t ((N • 𝟙 A : A ⟶ A).hom) = (N : ℤ_[p]) • 𝟙 G := by
  have : IsMonHom (𝟙 A.X ^ N) := inferInstanceAs (IsMonHom ((N • 𝟙 A : A ⟶ A).hom))
  exact t.map_pow_id N

theorem tmap_comp (T : Theory p) {k : Type} [Field k] [CharP k p] [PerfectRing k p] {G H K : PDivGroup p k}
    (f : G ⟶ H) (g : H ⟶ K) (y : T.M K) : T.map (f ≫ g) y = T.map f (T.map g y) := by
  have := (_root_.GlobalTheory.Dieu.base_functor_props p (fun _ _ _ => True) T.base k G H K trivial trivial trivial).2.1 f g
  exact LinearMap.congr_fun this y

theorem tmap_ppow_smul_id (T : Theory p) {k : Type} [Field k] [CharP k p] [PerfectRing k p] {H : PDivGroup p k}
    (a : ℕ) (y : T.M H) : T.map ((p : ℤ_[p]) ^ a • 𝟙 H) y = p ^ a • y := by
  have h := _root_.GlobalTheory.Dieu.base_functor_props p (fun _ _ _ => True) T.base k H H H trivial trivial trivial
  have h5 := h.2.2.2.2.1 a (𝟙 H) y
  have h1 := h.1
  change T.base.map trivial trivial _ y = _
  rw [h5, h1]
  rfl

theorem exists_ppow_quasiInverse {k : Type} [Field k] [CharP k p] {A B : AbVar k} (f : A ⟶ B)
    (hf : IsIsogeny f) (e : ℕ) (hdeg : deg f = p ^ e) :
    ∃ (a : ℕ) (f₁ : B ⟶ A), f ≫ f₁ = p ^ a • 𝟙 A ∧ f₁ ≫ f = p ^ a • 𝟙 B := by
  obtain ⟨N, f', hN, -, e1, e2⟩ := GlobalTheory.AV.AbVar.exists_quasiInverse_isogeny k A B f hf
  obtain ⟨a, m, hpm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' p (Fact.out : p.Prime).ne_one
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hpm (dvd_zero p))
  have hmk : (m : k) ≠ 0 := by rwa [Ne, CharP.cast_eq_zero_iff k p]
  have hcop : Nat.Coprime m (deg f) := by
    rw [hdeg]
    exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hpm).symm
  obtain ⟨f₁, hf₁⟩ := exists_nsmul_eq_of_kills_torsion k B A f' m hmk (fun y hy => by
    apply GlobalTheory.AV.KerInv.eq_one_of_coprime f hf m hm0 hcop (y ≫ f'.hom)
    · rw [Category.assoc, ← comp_hom, e2, nsmul_hom, id_hom, comp_id_pow_eq, pow_mul', hy, one_pow]
    · rw [← pow_comp_hom, hy, MonObj.one_comp])
  have hmz : ((m : ℤ)) ≠ 0 := by exact_mod_cast hm0.ne'
  refine ⟨a, f₁, ?_, ?_⟩
  · refine sub_eq_zero.1 (hom_torsionFree k A A (m : ℤ) _ hmz ?_)
    rw [smul_sub, natCast_zsmul, natCast_zsmul, ← Preadditive.comp_nsmul, ← hf₁, e1, smul_smul, mul_comm]
    exact sub_self _
  · refine sub_eq_zero.1 (hom_torsionFree k B B (m : ℤ) _ hmz ?_)
    rw [smul_sub, natCast_zsmul, natCast_zsmul, ← Preadditive.nsmul_comp, ← hf₁, e2, smul_smul, mul_comm]
    exact sub_self _

theorem exists_factor_of_range_le (T : Theory p) {k : Type} [Field k] [CharP k p] [PerfectRing k p]
    {A B C : AbVar k} {G H K : PDivGroup p k} (t : G.TorsionTower A.X) (t' : H.TorsionTower B.X)
    (t'' : K.TorsionTower C.X) (f : A ⟶ B) (g : A ⟶ C) (e : ℕ) (hf : IsIsogeny f) (hdeg : deg f = p ^ e)
    (hr : LinearMap.range (T.map (t.map t'' g.hom)) ≤ LinearMap.range (T.map (t.map t' f.hom))) :
    ∃ u : B ⟶ C, f ≫ u = g := by
  obtain ⟨a, f₁, h1, h2⟩ := exists_ppow_quasiInverse f hf e hdeg
  have hdiv : ∀ x, ∃ x', T.map (t'.map t'' (f₁ ≫ g).hom) x = p ^ a • x' := by
    intro x
    obtain ⟨y, hy⟩ := hr (LinearMap.mem_range_self _ x)
    refine ⟨y, ?_⟩
    have c1 : t'.map t'' (f₁ ≫ g).hom = t'.map t f₁.hom ≫ t.map t'' g.hom :=
      (t'.map_congr t'' (comp_hom f₁ g)).trans (t'.map_comp t t'' _ _)
    have c2 : t'.map t f₁.hom ≫ t.map t' f.hom = (p : ℤ_[p]) ^ a • 𝟙 H := by
      rw [← t'.map_comp t t', ← Nat.cast_pow, ← map_nsmul_id t']
      exact t'.map_congr t' ((comp_hom f₁ f).symm.trans (congrArg Hom.hom h2))
    rw [c1, tmap_comp, ← hy, ← tmap_comp, c2, tmap_ppow_smul_id]
  obtain ⟨u, hu⟩ := exists_eq_ppow_smul T t' t'' (f₁ ≫ g) a hdiv
  refine ⟨u, sub_eq_zero.1 (hom_torsionFree k A C ((p ^ a : ℕ) : ℤ) _ (by exact_mod_cast (pow_pos (Fact.out : p.Prime).pos a).ne') ?_)⟩
  rw [smul_sub, natCast_zsmul, natCast_zsmul, ← Preadditive.comp_nsmul, ← hu, ← Category.assoc, h1,
    Preadditive.nsmul_comp, Category.id_comp]
  exact sub_self _

theorem abVar_dieudonne_integral_length_factor : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (A B : AbVar k) (G H : PDivGroup p k) (t : G.TorsionTower A.X) (t' : H.TorsionTower B.X) (f : A ⟶ B), (∀ n : ℕ, (∀ m, ∃ m', T.map (t.map t' f.hom) m = p ^ n • m') → ∃ f' : A ⟶ B, f = p ^ n • f') ∧ (IsIsogeny f → IsIsog (t.map t' f.hom) ∧ Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map (t.map t' f.hom))) = padicValNat p (deg f)) ∧ ∀ (C : AbVar k) (K : PDivGroup p k) (t'' : K.TorsionTower C.X) (g : A ⟶ C) (e : ℕ), IsIsogeny f → deg f = p ^ e → LinearMap.range (T.map (t.map t'' g.hom)) ≤ LinearMap.range (T.map (t.map t' f.hom)) → ∃ u : B ⟶ C, f ≫ u = g := by
  intro p _ T k _ _ _ A B G H t t' f
  refine ⟨fun n h => exists_eq_ppow_smul T t t' f n h, fun hf => ?_,
    fun C K t'' g e hf hdeg hr => exists_factor_of_range_le T t t' t'' f g e hf hdeg hr⟩
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.Dieu.isIsog_hasLogDeg_map p k A B G H t t' f hf
  exact ⟨h1, _root_.GlobalTheory.Dieu.length_quot_range_map_eq_of_hasLogDeg p T k G H _ _ h1 h2⟩

end GlobalTheory.Dieu.AbVarDieu
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFamilyTrivialOfQuotientPullbackTrivial
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualInjPull

theorem smooth_of_dimLe {S : Scheme.{0}} {A C : Over S} (h : DimLe A C) {g : ℕ}
    (hA : SmoothOfRelativeDimension g A.hom) : SmoothOfRelativeDimension g C.hom := by
  have h1 : SmoothOfRelativeDimension g (pullback.snd A.hom (𝟙 S)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback A.hom (𝟙 S)) hA
  have h2 := h g S (𝟙 S) h1
  have sq : IsPullback (inv (pullback.fst C.hom (𝟙 S))) C.hom (pullback.snd C.hom (𝟙 S)) (𝟙 S) :=
    IsPullback.of_horiz_isIso ⟨by rw [IsIso.inv_comp_eq, Category.comp_id, pullback.condition, Category.comp_id]⟩
  exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback sq h2

theorem isIso_of_mono' {S : Scheme.{0}} {B B' : Over S} [GrpObj B] [GrpObj B'] (hB : IsAbelianScheme B)
    (hB' : IsAbelianScheme B') {g : ℕ} (hg : SmoothOfRelativeDimension g B.hom)
    (hg' : SmoothOfRelativeDimension g B'.hom) (x : B ⟶ B') [Mono x] : IsIso x := by
  have := hB.proper
  have := hB'.proper
  have := hB'.geomConnected
  have : Mono x.left := inferInstanceAs (Mono ((Over.forget S).map x))
  have : IsProper (x.left ≫ B'.hom) := by rw [Over.w]; infer_instance
  have : IsProper x.left := IsProper.of_comp x.left B'.hom
  have : IsClosedImmersion x.left := (IsClosedImmersion.iff_isProper_and_mono _).2 ⟨‹_›, ‹_›⟩
  have hs : Surjective B.hom := ⟨fun t => ⟨(η[B] : 𝟙_ (Over S) ⟶ B).left t, by
    rw [← Scheme.Hom.comp_apply, Over.w]; rfl⟩⟩
  have : Surjective (x.left ≫ B'.hom) := by rw [Over.w]; exact hs
  have : IsIso x.left :=
    GlobalTheory.AbMonoIsoAny.isIso_of_isClosedImmersion B'.hom x.left hg' (by rw [Over.w]; exact hg) le_rfl
  have : IsIso ((Over.forget _).map x) := ‹_›
  exact isIso_of_reflects_iso x (Over.forget _)

theorem evc_of_iso {S : Scheme.{0}} {A T X U Y : Over S} {M : LB (A ⊗ T).left} {N : LB (X ⊗ U).left}
    (hM : M.IsLB) (hN : N.IsLB) (f : A ⊗ T ⟶ X) (g : A ⊗ T ⟶ U) (e : LBIso M (ev N f g))
    (a : Y ⟶ A) (t : Y ⟶ T) : evc hM a t = evc hN (lift a t ≫ f) (lift a t ≫ g) := by
  have c : cls M hM = cls _ (pull_isLB hN _) := (cls_eq_iff hM (pull_isLB hN _)).2 e
  rw [← evc_ev hN f g (pull_isLB hN _) a t, evc, evc, c]

theorem triv_of_triv_pull : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' B : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj B] (g : ℕ) (P : LB (A ⊗ B).left) (P' : LB (A' ⊗ B).left) (q : A ⟶ A'), IsAbelianScheme A → IsAbelianScheme A' → IsAbelianScheme B → SmoothOfRelativeDimension g A'.hom → SmoothOfRelativeDimension g B.hom → IsDual A B P → IsMonHom q → P'.IsLB → IsAdditive P' → LBIso (ev P' (fst A B ≫ q) (snd A B)) P → ∀ (T : Over (Sp K)) (M : LB (A' ⊗ T).left), M.IsLB → IsAdditive M → Triv (ev M (fst A T ≫ q) (snd A T)) → Triv M := by
  intro K _ _ A A' B _ _ _ g P P' q hA hA' hB hgA' hgB hD hq hP' haP' eP T M hM haM hT
  obtain ⟨C, _, Q, hC, hdim, hQ⟩ := _root_.GlobalTheory.DualExist.exists_dual _ A' hA'
  have hgC : SmoothOfRelativeDimension g C.hom := smooth_of_dimLe hdim hgA'
  have hP := hD.isLB
  have hQl := hQ.isLB
  have hR : (ev Q (fst A C ≫ q) (snd A C)).IsLB := pull_isLB hQl _
  have haR : IsAdditive (ev Q (fst A C ≫ q) (snd A C)) := by
    refine (isAdditive_iff hR).2 fun Y a a' t ↦ ?_
    rw [evc_ev hQl, evc_ev hQl, evc_ev hQl]
    simp only [lift_fst_assoc, lift_snd, MonObj.mul_comp]
    exact (isAdditive_iff hQl).1 hQ.additive Y _ _ t
  obtain ⟨s, hs, -⟩ := hQ.univ B P' hP' haP'
  obtain ⟨r, hr, -⟩ := hD.univ C _ hR haR
  have hsr : s ≫ r = 𝟙 B := by
    refine GlobalTheory.AbDual.IsDual.eq_of_evc hD ?_
    have e1 := evc_of_iso hR hP _ _ hr (fst A B) (snd A B ≫ s)
    have e1' := evc_ev hQl (fst A C ≫ q) (snd A C) hR (fst A B) (snd A B ≫ s)
    have e2 := evc_of_iso hP' hQl _ _ hs (fst A B ≫ q) (snd A B)
    have e3 : evc hP' (fst A B ≫ q) (snd A B) = evc hP (fst A B) (snd A B) := by
      rw [← cls_ev hP' _ _ (pull_isLB hP' _), (cls_eq_iff _ hP).2 eP, evc, lift_fst_snd, Over.id_left, pull_id]
    simp only [lift_fst, lift_snd_assoc, lift_fst_assoc, lift_snd, Category.assoc] at e1 e1' e2
    rw [Category.comp_id, ← e3, e2, ← e1', e1]
  obtain ⟨c, hc, -⟩ := hQ.univ T M hM haM
  have hcr : c ≫ r = 1 := hD.eq_one _ ((triv_ev_iff hP _ _).2 (by
    have f1 := evc_of_iso hR hP _ _ hr (fst A T) (snd A T ≫ c)
    have f1' := evc_ev hQl (fst A C ≫ q) (snd A C) hR (fst A T) (snd A T ≫ c)
    have f2 := evc_of_iso hM hQl _ _ hc (fst A T ≫ q) (snd A T)
    have f3 := (triv_ev_iff hM _ _).1 hT
    simp only [lift_fst, lift_snd_assoc, lift_fst_assoc, lift_snd, Category.assoc] at f1 f1' f2
    rw [← f1, f1', ← f2, f3]))
  have h1r : (1 : T ⟶ C) ≫ r = 1 := hD.eq_one _ ((triv_ev_iff hP _ _).2 (by
    have f1 := evc_of_iso hR hP _ _ hr (fst A T) (snd A T ≫ (1 : T ⟶ C))
    have f1' := evc_ev hQl (fst A C ≫ q) (snd A C) hR (fst A T) (snd A T ≫ (1 : T ⟶ C))
    simp only [lift_fst, lift_snd_assoc, lift_fst_assoc, lift_snd, Category.assoc] at f1 f1'
    rw [← f1, f1', MonObj.comp_one, evc_one_right hQl hQ.zero]))
  haveI : IsSplitMono s := IsSplitMono.mk' ⟨r, hsr⟩
  haveI : IsIso s := isIso_of_mono' hB hC hgB hgC s
  have hrinv : r = inv s := (IsIso.inv_eq_of_hom_inv_id hsr).symm
  haveI : IsIso r := by rw [hrinv]; infer_instance
  have hc1 : c = 1 := (cancel_mono r).1 (hcr.trans h1r.symm)
  refine (cls_eq_zero_iff hM).1 ?_
  rw [(cls_eq_iff hM (pull_isLB hQl _)).2 hc, cls_ev hQl, hc1, MonObj.comp_one, evc_one_right hQl hQ.zero]
end GlobalTheory.DualInjPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelSmallSectionsChangeOfMetric
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp.ChangeSing

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
  {Y : Scheme.{0}} [IsIntegral Y] {q : Y ⟶ Sp k}

theorem up_pull_isometric (L : HermLB p) (u : SmFn p) (ρ : Y ⟶ X) (hρ : ρ ≫ p = q) :
    (up (L.pull ρ hρ) (u.pull ρ hρ)).Isometric ((up L u).pull ρ hρ) := by
  refine HermLB.isometric_of_eqOn ?_
  intro σ a y _
  erw [Weight.pull_φ]
  exact (congrArg (· + u.u σ (Points.PtsOver.map ρ hρ (spMap σ) y)) (Weight.pull_φ (L.φ σ) ρ hρ a y)).symm

theorem ballIn_map (P : Pair p) (Q : Pair q) (e : X.functionField →+* Y.functionField) (ρ : Y ⟶ X) (hρ : ρ ≫ p = q)
    (hs : ∀ σ : k →+* ℂ, Function.Surjective (Points.PtsOver.map ρ hρ (spMap σ) : CxPts q σ → CxPts p σ))
    (Λ : AddSubgroup X.functionField) (a b : ℤ)
    (hn : ∀ f ∈ Λ, ∀ (σ : k →+* ℂ) (y : CxPts q σ), Q.nu a b σ y (e f) = P.nu a b σ (Points.PtsOver.map ρ hρ (spMap σ) y) f)
    (R : ℝ) : ballIn Q (Λ.map e.toAddMonoidHom) a b R = e '' ballIn P Λ a b R := by
  ext g
  constructor
  · rintro ⟨⟨f, hf, rfl⟩, hR⟩
    refine ⟨f, ⟨hf, fun σ x => ?_⟩, rfl⟩
    obtain ⟨y, rfl⟩ := hs σ x
    rw [← hn f hf σ y]
    exact hR σ y
  · rintro ⟨f, ⟨hf, hR⟩, rfl⟩
    refine ⟨⟨f, hf, rfl⟩, fun σ y => ?_⟩
    rw [hn f hf σ y]
    exact hR σ _

theorem ncard_ballIn_map (P : Pair p) (Q : Pair q) (e : X.functionField →+* Y.functionField) (ρ : Y ⟶ X) (hρ : ρ ≫ p = q)
    (hs : ∀ σ : k →+* ℂ, Function.Surjective (Points.PtsOver.map ρ hρ (spMap σ) : CxPts q σ → CxPts p σ))
    (Λ : AddSubgroup X.functionField) (a b : ℤ)
    (hn : ∀ f ∈ Λ, ∀ (σ : k →+* ℂ) (y : CxPts q σ), Q.nu a b σ y (e f) = P.nu a b σ (Points.PtsOver.map ρ hρ (spMap σ) y) f)
    (R : ℝ) : (ballIn Q (Λ.map e.toAddMonoidHom) a b R).ncard = (ballIn P Λ a b R).ncard := by
  rw [ballIn_map P Q e ρ hρ hs Λ a b hn R]
  exact Set.ncard_image_of_injective _ e.injective

theorem goodFam_map (P : Pair p) (Q : Pair q) (e : X.functionField →+* Y.functionField) (ρ : Y ⟶ X) (hρ : ρ ≫ p = q)
    (hs : ∀ σ : k →+* ℂ, Function.Surjective (Points.PtsOver.map ρ hρ (spMap σ) : CxPts q σ → CxPts p σ))
    (he : ∀ (a b : ℤ), ∀ f ∈ P.H a b, e f ∈ Q.H a b ∧ ∀ (σ : k →+* ℂ) (y : CxPts q σ),
      Q.nu a b σ y (e f) = P.nu a b σ (Points.PtsOver.map ρ hρ (spMap σ) y) f)
    (D : ℕ) (g : ℝ) (Λ : ℕ → AddSubgroup X.functionField) (h : GoodFam P D g Λ) :
    GoodFam Q D g (fun m => (Λ m).map e.toAddMonoidHom) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m
    rintro _ ⟨f, hf, rfl⟩
    exact (he m 1 f (h.le m hf)).1
  · intro m
    obtain ⟨s, hs', hsFinite⟩ := (AddSubgroup.fg_iff (Λ m)).mp (h.fg m)
    refine (AddSubgroup.fg_iff _).mpr ⟨e '' s, ?_, hsFinite.image e⟩
    rw [← hs', AddMonoidHom.map_closure]
    rfl
  · obtain ⟨C, hC, hCm⟩ := h.small
    refine ⟨C, hC, fun m hm => ?_⟩
    have hn : ∀ f ∈ Λ m, ∀ (σ : k →+* ℂ) (y : CxPts q σ),
        Q.nu m 1 σ y (e f) = P.nu m 1 σ (Points.PtsOver.map ρ hρ (spMap σ) y) f :=
      fun f hf => (he m 1 f (h.le m hf)).2
    rw [ballIn_map P Q e ρ hρ hs (Λ m) m 1 hn]
    exact (AddSubgroup.map_mono (hCm m hm)).trans
      (AddMonoidHom.map_closure e.toAddMonoidHom (ballIn P (Λ m) m 1 (C ^ m))).le
  · have e' : ∀ m, Module.finrank ℤ ((Λ m).map e.toAddMonoidHom) = Module.finrank ℤ (Λ m) := fun m =>
      ((AddSubgroup.equivMapOfInjective (Λ m) e.toAddMonoidHom e.injective).toIntLinearEquiv.finrank_eq).symm
    simp only [e']
    exact h.rank

end GlobalTheory.HSAmp.ChangeSing

namespace GlobalTheory.HSAmp.ChangeSing

theorem count_change_of_principalisation : GlobalTheory.Published.Principalisation → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (a : ℝ), P.L.SemiPos D → P.L.IsSelfInter a → GoodFam P D (gdeg P.L D / D.factorial) (fun m => P.H m 1) → ∃ t₀ : ℝ, ∀ (u : SmFn p) (B a' : ℝ), 0 ≤ B → (∀ σ y, |u.u σ y| ≤ B) → (up P.L u).SemiPos D → (up P.L u).IsSelfInter a' → ∀ t : ℝ, t₀ + B ≤ t → Tendsto (fun m : ℕ => (Real.log ((ballIn (upperParabolic P u) (P.H m 1) m 1 (Real.exp (t * m))).ncard : ℝ) - Real.log ((ballIn P (P.H m 1) m 1 (Real.exp (t * m))).ncard : ℝ)) / (m : ℝ) ^ (D + 1)) atTop (𝓝 ((a' - a) / (D + 1).factorial)) := by
  intro hPr k _ X _ p D hX P a hsp hsi hgf
  have hC : Published.ArCalc := MixHt.arCalc_of_principalisation hPr
  obtain ⟨Y, hY, ρ, hYa, hYs, hgen, hdeg⟩ := GenRes.exists_birational_genSmooth hPr k X p D hX
  obtain ⟨Q, e, hQL, -, he⟩ := _root_.GlobalTheory.HSAmp.pair_pull k X p Y (ρ ≫ p) ρ rfl hgen P
  have hs : ∀ σ : k →+* ℂ, Function.Surjective
      (Points.PtsOver.map ρ rfl (spMap σ) : CxPts (ρ ≫ p) σ → CxPts p σ) :=
    _root_.GlobalTheory.DomSurj.surjective_cxPts_map k X p D hX Y (ρ ≫ p) D hYa ρ rfl hgen
  have hne : ρ.residueDegree (genericPoint Y) ≠ 0 := by rw [hdeg]; exact one_ne_zero
  have hproj := hC.2.2.2.2.1 k X Y p (ρ ≫ p) D hX hYa ρ rfl hgen hne
  have hdeg' : ((ρ.residueDegree (genericPoint Y) : ℕ) : ℝ) = 1 := by rw [hdeg]; simp
  have hQsp : Q.L.SemiPos D := by
    rw [hQL]; exact _root_.GlobalTheory.SemiPullBir.semiPos_pull k X p D hX Y (ρ ≫ p) hYa ρ rfl hgen hdeg P.L hsp
  have hQsi : Q.L.IsSelfInter a := by
    have h := hproj.1 P.L a hsi
    rw [hdeg', one_mul] at h
    rw [hQL]; exact h
  have hQg : gdeg Q.L D = gdeg P.L D := by
    rw [hQL, CovTest.gdegPull k X Y p (ρ ≫ p) D hX hYa ρ rfl hgen hne, hdeg', one_mul]
  have hgf' := goodFam_map P Q e ρ rfl hs he D _ _ hgf
  rw [← hQg] at hgf'
  obtain ⟨t₀, ht⟩ := _root_.GlobalTheory.HSAmp.tendsto_logCount_sub_up hC k Y (ρ ≫ p) D hYa hYs Q a hQsp hQsi _ hgf'
  refine ⟨t₀, fun u B a' hB hu husp husi t ht' => ?_⟩
  have hiso : (up Q.L (u.pull ρ rfl)).Isometric ((up P.L u).pull ρ rfl) := by
    rw [hQL]; exact up_pull_isometric P.L u ρ rfl
  have h1 : (up Q.L (u.pull ρ rfl)).SemiPos D :=
    HermLB.Isometric.semiPos _ _ D hiso.symm (_root_.GlobalTheory.SemiPullBir.semiPos_pull k X p D hX Y (ρ ≫ p) hYa ρ rfl hgen hdeg _ husp)
  have h2 : (up Q.L (u.pull ρ rfl)).IsSelfInter a' := by
    have h := hproj.1 (up P.L u) a' husi
    rw [hdeg', one_mul] at h
    exact hiso.symm.isSelfInter hYa h
  have h3 := ht (u.pull ρ rfl) B a' hB (fun σ y => hu σ _) h1 h2 t ht'
  have hnP : ∀ m : ℕ, ∀ f ∈ P.H (m : ℤ) 1, ∀ (σ : k →+* ℂ) (y : CxPts (ρ ≫ p) σ),
      Q.nu m 1 σ y (e f) = P.nu m 1 σ (Points.PtsOver.map ρ rfl (spMap σ) y) f :=
    fun m f hf => (he m 1 f hf).2
  have hnU : ∀ m : ℕ, ∀ f ∈ P.H (m : ℤ) 1, ∀ (σ : k →+* ℂ) (y : CxPts (ρ ≫ p) σ),
      (upperParabolic Q (u.pull ρ rfl)).nu m 1 σ y (e f) =
        (upperParabolic P u).nu m 1 σ (Points.PtsOver.map ρ rfl (spMap σ) y) f := by
    intro m f hf σ y
    rw [((_root_.GlobalTheory.HSAmp.upAtPrime_groups_values_norms k Y (ρ ≫ p) Q (u.pull ρ rfl) m 1).2.2 σ y (e f)).2,
      ((_root_.GlobalTheory.HSAmp.upAtPrime_groups_values_norms k X p P u m 1).2.2 σ _ f).2, hnP m f hf σ y]
    rfl
  refine h3.congr fun m => ?_
  rw [ncard_ballIn_map (upperParabolic P u) (upperParabolic Q (u.pull ρ rfl)) e ρ rfl hs _ _ _ (hnU m),
    ncard_ballIn_map P Q e ρ rfl hs _ _ _ (hnP m)]

end GlobalTheory.HSAmp.ChangeSing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalChartResidueFieldDimensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonicalChart_residueField_dimension : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), Canon C → ((residue (ChartRing k m e)).comp C.b).EssFiniteType ∧ (letI := ((residue (ChartRing k m e)).comp C.b).toAlgebra; ((m + e : ℕ) : Cardinal) + Algebra.trdeg c.F (ResidueField (ChartRing k m e)) = Dw.dim) := by
  first | exact @GlobalTheory.UCanon.canon_residue_dim | exact GlobalTheory.UCanon.canon_residue_dim | (intros; apply GlobalTheory.UCanon.canon_residue_dim <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyBaseEqOfMatchingPullbacksStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonicalFamily_base_eq_of_matching_pullbacks : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ f₁ f₂ : R →+* V, Function.Injective f₁ → Function.Injective f₂ → IsLocalHom f₁ → IsLocalHom f₂ → ∀ (D₁ D₂ : DegData V (maximalIdeal V)) (hD₁ : IsPullDeg f₁ C.P.D.toPre D₁.toPre) (hD₂ : IsPullDeg f₂ C.P.D.toPre D₂.toPre) (j₁ j₂ : (AlgebraicClosure (FractionRing R)) →+* (AlgebraicClosure (FractionRing V))) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (φ' : D₁.toPre.X ≃+ D₂.toPre.X), GlobalTheory.TInj.Ext f₁ j₁ → GlobalTheory.TInj.Ext f₂ j₂ → GlobalTheory.TInj.Match D₁.toPre D₂.toPre b φ' (AlgebraicClosure (FractionRing V)) → (∀ p₀ : QkPt C.P.D.toPre (AlgebraicClosure (FractionRing R)) l.M', ∃ (p₁ : QkPt D₁.toPre (AlgebraicClosure (FractionRing V)) l.M') (p₂ : QkPt D₂.toPre (AlgebraicClosure (FractionRing V)) l.M'), p₁.y = hD₁.xe.symm p₀.y ∧ GlobalTheory.TInj.Tr f₁ hD₁ j₁ p₀.g p₁.g ∧ p₂.y = hD₂.xe.symm p₀.y ∧ GlobalTheory.TInj.Tr f₂ hD₂ j₂ p₀.g p₂.g ∧ GlobalTheory.TInj.QImg b φ' p₁ p₂) → (letI := H.starRing; ∀ x : 𝓞 E, ∃ (a₁ : D₁.toPre.P.A ⟶ D₁.toPre.P.A) (a₂ : D₂.toPre.P.A ⟶ D₂.toPre.P.A), a₁ ≫ hD₁.e.hom = hD₁.e.hom ≫ (Over.pullback (specOf f₁)).map (C.P.oD.onB.act x) ∧ a₂ ≫ hD₂.e.hom = hD₂.e.hom ≫ (Over.pullback (specOf f₂)).map (C.P.oD.onB.act x) ∧ a₁ ≫ b = b ≫ a₂) → (∀ y : C.P.D.toPre.X, hD₂.xe (φ' (hD₁.xe.symm y)) = y) → f₁.comp C.b = f₂.comp C.b → f₁.comp (Cn.ψ.comp MvPolynomial.C) = f₂.comp (Cn.ψ.comp MvPolynomial.C) := by
  first | exact @GlobalTheory.UCanon.PairBase.base_eq_of_match | exact GlobalTheory.UCanon.PairBase.base_eq_of_match | (intros; apply GlobalTheory.UCanon.PairBase.base_eq_of_match <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyHasPointRigidCoordinates
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UCanon.canon_hasRigidCoords : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), HasRigidCoords C := by
  intro E _ _ _ H Dw l Xo c φ R _ _ _ hB C Cn
  obtain ⟨ε', τ₀, hε', hFB, hTau⟩ := _root_.GlobalTheory.UCanon.PerCoord.main Xo c φ R hB C Cn
  refine ⟨Cn.N, fun k => Cn.ψ (MvPolynomial.X k), ε', τ₀, fun i => Cn.bd i, ?_, fun k => Cn.tor k, hTau, ?_⟩
  · intro i
    rw [hε', Cn.cone i]
  · intro K _ _ ev k₀ hk₀ hemb hsep
    obtain ⟨h1, h2, h3⟩ := hsep
    have hbase : ∀ a, ev ((Cn.ψ.comp MvPolynomial.C) a) ∈ k₀ :=
      GlobalTheory.T.canonicalFamily_base_value_mem_descended_point Cn.L C.P.D.toPre C.P.oD (Cn.ψ.comp MvPolynomial.C) (fun k => Cn.ψ (MvPolynomial.X k))
        (fun k => (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X)) Cn.e Cn.data K ev k₀ hk₀ h2
    have htor := h3 Cn.L.W (Cn.ψ.comp MvPolynomial.C) hFB hbase
    have hX : ∀ k, ev (Cn.ψ (MvPolynomial.X k)) ∈ k₀ := by
      rintro (i | i)
      · have := h1 i
        simp only at this
        rw [this]; exact k₀.zero_mem
      · exact htor i
    have hall : ∀ a : MvPolynomial (Fin C.m ⊕ Fin Cn.N) Cn.L.W, ev (Cn.ψ a) ∈ k₀ := by
      intro a
      induction a using MvPolynomial.induction_on with
      | C a => exact hbase a
      | add p q hp hq => rw [map_add (f := _), map_add (f := _)]; exact k₀.add_mem hp hq
      | mul_X p k hp => rw [map_mul, map_mul]; exact k₀.mul_mem hp (hX k)
    have hft : ((MvPolynomial.C : Cn.L.W →+* MvPolynomial (Fin C.m ⊕ Fin Cn.N) Cn.L.W).comp Cn.L.b).EssFiniteType := by
      refine RingHom.EssFiniteType.comp Cn.L.ft ?_
      exact (RingHom.FiniteType.essFiniteType (by
        rw [← MvPolynomial.algebraMap_eq]
        exact RingHom.finiteType_algebraMap.mpr inferInstance))
    exact GlobalTheory.T.closedPoint_of_values_in_small_algClosed c.F (MvPolynomial (Fin C.m ⊕ Fin Cn.N) Cn.L.W) R K (MvPolynomial.C.comp Cn.L.b) hft Cn.ψ Cn.compl
      ev k₀ hemb hall
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyEqOfIsogenyIntertwines
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem intCast_comp_cpisog {K : Type} [Field K] {A B : AbVar K} (n : ℤ) (u : A ⟶ B) :
    (n : End A).asHom ≫ u = n • u := by
  rw [← zsmul_one]
  change (n • 𝟙 A) ≫ u = n • u
  rw [Preadditive.zsmul_comp, Category.id_comp]

theorem comp_intCast_cpisog {K : Type} [Field K] {A B : AbVar K} (n : ℤ) (u : A ⟶ B) :
    u ≫ (n : End B).asHom = n • u := by
  rw [← zsmul_one]
  change u ≫ (n • 𝟙 B) = n • u
  rw [Preadditive.comp_zsmul, Category.comp_id]

theorem charpoly_eq_of_isogeny_intertwines :
    ∀ (K : Type) [Field K] (A B : AbVar K) (u : A ⟶ B) (f : End A) (g : End B),
      IsIsogeny u → f.asHom ≫ u = u ≫ g.asHom → charpoly f = charpoly g := by
  intro K _ A B u f g hu hfg
  obtain ⟨hdim, -, hpos, -⟩ := GlobalTheory.AV.AbVar.isogeny_flat_finrank K A B u hu
  have key : ∀ n : ℤ, deg ((n : End A) - f).asHom = deg ((n : End B) - g).asHom := by
    intro n
    have hc : ((n : End A) - f).asHom ≫ u = u ≫ ((n : End B) - g).asHom := by
      rw [End.sub_asHom, End.sub_asHom, Preadditive.sub_comp, Preadditive.comp_sub,
        intCast_comp_cpisog, comp_intCast_cpisog]
      exact congrArg (n • u - ·) hfg
    have h1 := (GlobalTheory.AV.AbVar.isIsogeny_comp_iff_and_deg_comp K A A B
      ((n : End A) - f).asHom u rfl hdim).2
    have h2 := (GlobalTheory.AV.AbVar.isIsogeny_comp_iff_and_deg_comp K A B B
      u ((n : End B) - g).asHom hdim rfl).2
    rw [hc, h2, mul_comm] at h1
    exact (Nat.eq_of_mul_eq_mul_right hpos h1).symm
  obtain ⟨⟨hm, hd, hev⟩, -⟩ := GlobalTheory.T.abelianVarietyEndCharpoly_spec K A f
  have hg : IsCharpoly g (charpoly f) := ⟨hm, by rw [hd, hdim], fun n => by rw [hev n, key n]⟩
  exact (GlobalTheory.T.abelianVarietyEndCharpoly_spec K B g).2 _ hg

end GlobalTheory.AV.AbVar
end

