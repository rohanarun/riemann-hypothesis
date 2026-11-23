module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.BlockTriangularOfSubOne
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0294
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0625
public import Formalism.LocalToGlobal.IndefiniteReal.LinksW
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealSideCharacterMatch
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0196
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrincipalCongruenceFixedVectorsLeSmoothVectors
section
noncomputable section

namespace GlobalTheory.SerSys.TameGen

open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp CategoryTheory
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

def IsSC (ρ : GLRep g) : Prop := 0 < ρ.1 ∧ IsIrrRep ρ.2.ρ ∧ PRep.IsSupercuspidal ρ.2.ρ

def Inflates {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) ℚ_[g]) V)
    (τ : FDRep ℂ (Gn g n)) : Prop :=
  ∃ φ : τ →ₗ[ℂ] V, φ ≠ 0 ∧ ∀ (k : GL (Fin n) ℤ_[g]) (w : τ), φ (τ.ρ (red g n k) w) = π (inc g n k) (φ w)

def liftPoly (teich : Formalism.CyclotomicNorms.Fbar g → ℂ) (f : (ZMod g)[X]) : ℂ[X] :=
  ((Formalism.CyclotomicNorms.rootsBar f).map fun x => X - C (teich x)).prod

def SupportCompat {LP : Type} (ine : LP → ℂ[X]) (rec : GLRep g → LP) : Prop :=
  ∀ π : GLRep g, IsIrrRep π.2.ρ → PRep.IsSmooth π.2.ρ →
    ∃ L : List (GLRep g), InInd π L ∧ (∀ ρ ∈ L, IsSC ρ) ∧ ine (rec π) = (L.map fun ρ => ine (rec ρ)).prod

def DepthZeroCuspidal (g : ℕ) [Fact g.Prime] : Prop :=
  ∀ ρ : GLRep g, IsSC ρ → fixK1 ρ.2.ρ ≠ ⊥ → FiniteGL.IsCuspidal (repK ρ.2.ρ)

theorem liftPoly_one (teich : Formalism.CyclotomicNorms.Fbar g → ℂ) : liftPoly teich (1 : (ZMod g)[X]) = 1 := by
  simp [liftPoly, Formalism.CyclotomicNorms.rootsBar]

theorem liftPoly_mul (teich : Formalism.CyclotomicNorms.Fbar g → ℂ) {f f' : (ZMod g)[X]} (hf : f ≠ 0) (hf' : f' ≠ 0) :
    liftPoly teich (f * f') = liftPoly teich f * liftPoly teich f' := by
  unfold liftPoly Formalism.CyclotomicNorms.rootsBar
  rw [Polynomial.map_mul, roots_mul (mul_ne_zero (map_ne_zero hf) (map_ne_zero hf')), Multiset.map_add (f := _),
    Multiset.prod_add]

theorem Has.monic {S : Sys g} {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin n) ℚ_[g]) V} {f : (ZMod g)[X]} (h : Has S π f) : f.Monic := by
  obtain ⟨v, -, hv⟩ := h
  refine (S.label n f fun e => hv ?_).1
  simp [e, actK]

theorem exists_simple {G W : Type} [Group G] [Fintype G] [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W)
    (e : MonoidAlgebra ℂ G) (he : ∀ a, e * a = a * e) (w : W) (hw : w ≠ 0) (hew : σ.asAlgebraHom e w = w) :
    ∃ (τ : FDRep ℂ G) (φ : τ →ₗ[ℂ] W), Simple τ ∧ Function.Injective φ ∧ (∀ x u, φ (τ.ρ x u) = σ x (φ u)) ∧
      Representation.asAlgebraHom τ.ρ e = 1 := by
  let P : Submodule ℂ W → Prop := fun U => U ≠ ⊥ ∧ FiniteDimensional ℂ U ∧ (∀ x, ∀ u ∈ U, σ x u ∈ U) ∧
    ∀ u ∈ U, σ.asAlgebraHom e u = u
  have hex : ∃ m, ∃ U, P U ∧ Module.finrank ℂ U = m := by
    refine ⟨_, Submodule.span ℂ (Set.range fun x => σ x w), ⟨?_, ?_, ?_, ?_⟩, rfl⟩
    · intro h
      exact hw (by simpa using (Submodule.span_eq_bot.1 h) _ ⟨1, rfl⟩)
    · exact FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
    · intro x u hu
      refine (show _ ≤ Submodule.comap (σ x) (Submodule.span ℂ (Set.range fun x => σ x w)) from
        Submodule.span_le.2 ?_) hu
      rintro _ ⟨y, rfl⟩
      exact Submodule.subset_span ⟨x * y, by simp⟩
    · intro u hu
      refine (show _ ≤ LinearMap.eqLocus (σ.asAlgebraHom e) LinearMap.id from Submodule.span_le.2 ?_) hu
      rintro _ ⟨y, rfl⟩
      show σ.asAlgebraHom e (σ y w) = σ y w
      rw [← Representation.asAlgebraHom_single_one, ← Module.End.mul_apply, ← map_mul, he, map_mul,
        Module.End.mul_apply, hew]
  obtain ⟨U, ⟨h0, hfin, hst, hfix⟩, hm⟩ := Nat.find_spec hex
  have hmin : ∀ U', P U' → Module.finrank ℂ U ≤ Module.finrank ℂ U' := fun U' h =>
    hm ▸ Nat.find_min' hex ⟨U', h, rfl⟩
  let σU : Representation ℂ G U := PRep.sub σ U hst
  have hirr : IsIrrRep σU := by
    refine ⟨Submodule.nontrivial_iff_ne_bot.2 h0, fun T hT => or_iff_not_imp_left.2 fun hT0 => ?_⟩
    have hP : P (T.map U.subtype) := by
      refine ⟨fun h => hT0 (Submodule.map_injective_of_injective U.injective_subtype (by simpa using h)), inferInstance, ?_, ?_⟩
      · rintro x _ ⟨u, hu, rfl⟩
        exact ⟨_, hT x u hu, rfl⟩
      · rintro _ ⟨u, -, rfl⟩
        exact hfix _ u.2
    have := hmin _ hP
    rw [Submodule.finrank_map_subtype_eq] at this
    exact Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le T) this)
  refine ⟨FDRep.of σU, U.subtype, ?_, U.injective_subtype, fun _ _ => rfl, ?_⟩
  · have := (Model.isIrrRep_iff σU).1 hirr
    rw [FDRep.simple_iff_char_is_norm_one]
    have hc : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
    have := invertibleOfNonzero hc
    have h := Representation.char_orthonormal σU σU
    rw [if_pos ⟨Representation.Equiv.refl σU⟩, inv_mul_eq_one₀ hc] at h
    exact h.symm
  · refine LinearMap.ext fun u => Subtype.ext ?_
    refine Eq.trans ?_ (hfix _ u.2)
    rw [alg_apply, alg_apply]
    exact (Submodule.coe_sum _ _ _).trans rfl

theorem exists_simple_of_has (S : Sys g) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (f : (ZMod g)[X]) (h : Has S π f) :
    ∃ (τ : FDRep ℂ (Gn g n)) (φ : τ →ₗ[ℂ] fixK1 π), Simple τ ∧ Function.Injective φ ∧
      (∀ x u, φ (τ.ρ x u) = repK π x (φ u)) ∧ Representation.asAlgebraHom τ.ρ (S.e n f) = 1 := by
  obtain ⟨v, hv, hne⟩ := h
  refine exists_simple (repK π) (S.e n f) (S.central n f) ((repK π).asAlgebraHom (S.e n f) ⟨v, hv⟩)
    (fun e => hne ?_) ?_
  · rw [← repK_alg π _ ⟨v, hv⟩, e]; rfl
  · rw [← Module.End.mul_apply, ← map_mul, S.idem]

def LabelsCusp (S : Sys g) (L : LabelDatum g) : Prop :=
  ∀ (d : ℕ) (τ : FDRep ℂ (Gn g d)) (P : (ZMod g)[X]), IsCuspOf L P τ.character →
    Representation.asAlgebraHom τ.ρ (S.e d P) ≠ 0

theorem mem_unipRadical_iff {d a : ℕ} (had : a < d) (x : Gn g d) :
    x ∈ FiniteGL.unipRadical (ZMod g) (FiniteGL.twoBlocks d a) ↔
      InPar a (x : Mt g d) ∧ tl a (x : Mt g d) = ((1 : Gn g a) : Mt g a) ∧
        br a (d - a) (x : Mt g d) = ((1 : Gn g (d - a)) : Mt g (d - a)) := by
  rw [FiniteGL.mem_unipRadical]
  simp only [FiniteGL.twoBlocks, Matrix.sub_apply, sub_eq_zero, Units.val_one]
  constructor
  · intro h
    refine ⟨fun i j hj hi => ?_, ?_, ?_⟩
    · rw [h i j (by simp [hj]), Matrix.one_apply_ne (fun e => by subst e; omega)]
    · ext i j
      have hi : (i : ℕ) < d := by omega
      have hj : (j : ℕ) < d := by omega
      simp only [tl, Formalism.MainNotions.ArithmeticCylinders.entN, hi, hj, and_self, dif_pos]
      rw [h _ _ (by simp)]
      simp [Matrix.one_apply, Fin.ext_iff]
    · ext i j
      have hi : a + (i : ℕ) < d := by omega
      have hj : a + (j : ℕ) < d := by omega
      simp only [br, Formalism.MainNotions.ArithmeticCylinders.entN, hi, hj, and_self, dif_pos]
      rw [h _ _ (by simp)]
      simp [Matrix.one_apply, Fin.ext_iff]
  · rintro ⟨h0, h1, h2⟩ i j hij
    by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a
    · have := congrFun (congrFun h1 ⟨i, hi⟩) ⟨j, hj⟩
      simpa [tl, Formalism.MainNotions.ArithmeticCylinders.entN, Matrix.one_apply, Fin.ext_iff] using this
    · simp [hi, hj] at hij
    · rw [h0 i j hj (by omega), Matrix.one_apply_ne (fun e => by subst e; omega)]
    · have := congrFun (congrFun h2 ⟨i - a, by omega⟩) ⟨j - a, by omega⟩
      have ei : a + (i - a) = i := by omega
      have ej : a + (j - a) = j := by omega
      have e : ((i : ℕ) - a = j - a) ↔ (i : ℕ) = j := by omega
      simpa [br, Formalism.MainNotions.ArithmeticCylinders.entN, Matrix.one_apply, Fin.ext_iff, ei, ej, e] using this

theorem isCusp_character {d : ℕ} (hd : 0 < d) (τ : FDRep ℂ (Gn g d)) (hs : Simple τ)
    (hc : FiniteGL.IsCuspidal τ.ρ) : IsCusp τ.character := by
  refine ⟨hd, ⟨τ, hs, fun _ => rfl⟩, fun a h0 had => ?_⟩
  set U := FiniteGL.unipRadical (ZMod g) (FiniteGL.twoBlocks d a)
  have hz : ∑ u : U, τ.ρ u = 0 := by
    refine LinearMap.ext fun v => (FiniteGL.isCuspidal_iff_twoBlocks τ.ρ).1 hc a h0 had _ fun x hx => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [LinearMap.sum_apply, map_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft (⟨x, hx⟩ : U)) _ _ fun u => ?_
    simp
  have ht := congrArg (LinearMap.trace ℂ τ) hz
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_zero] at ht
  unfold res
  rw [← Finset.sum_filter, Finset.sum_subtype (p := fun x => x ∈ U) _
    (fun x => by rw [mem_unipRadical_iff had]; simp) τ.character]
  exact mul_eq_zero_of_right _ ht

theorem principalCongruenceFixedVectors_le_smoothVectors {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) : fixK1 π ≤ PRep.smoothPart π := by
  intro v hv
  let T : Subgroup (GL (Fin n) ℚ_[g]) :=
    { carrier := {x | π x v = v}
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_ofPred_eq, map_mul, Module.End.mul_apply] at *
        rw [hy, hx]
      one_mem' := by simp
      inv_mem' := by
        intro x hx
        simp only [Set.mem_ofPred_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul]; simp }
  have ho : IsOpen {x : GL (Fin n) ℚ_[g] | ∀ i j, ‖(x.val - 1) i j‖ < 1} := by
    simp only [Set.ofPred_forall]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => isOpen_lt ?_ continuous_const
    exact ((Units.continuous_val.sub continuous_const).matrix_elem i j).norm
  refine T.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset (ho.mem_nhds (by simp)) fun x hx => ?_)
  let N : Matrix (Fin n) (Fin n) ℤ_[g] := Matrix.of fun i j => ⟨(x.val - 1) i j, (hx i j).le⟩
  have hN : (PadicInt.toZMod (p := g)).mapMatrix N = 0 := by
    ext i j
    have : N i j ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by
      rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
      exact hx i j
    exact this
  have hM : (PadicInt.toZMod (p := g)).mapMatrix (N + 1) = 1 := by rw [map_add (f := _), hN, map_one, zero_add]
  have hd : IsUnit (N + 1).det := by
    by_contra h
    have h1 : (N + 1).det ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by
      rw [PadicInt.ker_toZMod]; exact h
    rw [RingHom.mem_ker, RingHom.map_det, hM] at h1
    simp at h1
  let k : GL (Fin n) ℤ_[g] := ((Matrix.isUnit_iff_isUnit_det _).2 hd).unit
  have e1 : red g n k = 1 := Units.ext hM
  have e2 : inc g n k = x := by
    refine Units.ext ?_
    change (algebraMap ℤ_[g] ℚ_[g]).mapMatrix (N + 1) = x.val
    rw [map_add (f := _), map_one]
    exact (congrArg (· + 1) (show (algebraMap ℤ_[g] ℚ_[g]).mapMatrix N = x.val - 1 from rfl)).trans
      (sub_add_cancel _ _)
  exact e2 ▸ (Model.mem_principalCongruenceFixedVectors_iff π v).1 hv k e1

end GlobalTheory.SerSys.TameGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatMatExists
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistCharChange
open Formalism.IndefR.Lev

theorem ratMat_exists {D : D7} (V : HSp D) (γ : GQ V) : ∃ γE, Bridge.IsRatMat V γ γE := by
  have h := Subgroup.mem_subgroupOf.1 γ.2
  obtain ⟨γE, -, e⟩ := Subgroup.mem_map.1 h
  exact ⟨γE, e.symm⟩

theorem flag_vals {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (hcg : ∀ j, j < L.s → ∀ PP ∈ L.Pg, ∀ x, ∃ a, D.what₂.embLL a = ((L.cg (j + 1) PP x : ℂˣ) : ℂ))
    (hxq : ∀ PP ∈ L.Q, ∀ x, ∃ a, D.what₂.embLL a = ((L.xq PP x : ℂˣ) : ℂ)) (x) :
    ∃ a, D.what₂.embLL a = ((levFn β (flagL L) x : ℂˣ) : ℂ) := by
  have h1 : (flagL L).P.chi = 1 := rfl
  unfold levFn
  rw [h1, subgroupCharExtension_one_apply, one_mul]
  refine RingHom.mem_fieldRange.1 ?_
  simp only [Units.val_mul, Units.coe_prod]
  refine Subfield.mul_mem _ (Subfield.prod_mem _ fun PP hP => Subfield.prod_mem _ fun j hj => ?_)
    (Subfield.prod_mem _ fun PP hP => ?_)
  · obtain ⟨a, ha⟩ := hcg j (Finset.mem_range.1 hj) PP hP _
    exact RingHom.mem_fieldRange.2 ⟨a, ha⟩
  · obtain ⟨a, ha⟩ := hxq PP hP _
    exact RingHom.mem_fieldRange.2 ⟨a, ha⟩

end GlobalTheory.TwistCharChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalFormLengthEqDefiniteFamily
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

noncomputable section

namespace GlobalTheory.EtaJoin.Side

theorem length_quot_map {R M M' : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (f : M →ₗ[R] M') (hf : Function.Injective f) (P Q : Submodule R M) :
    Module.length R (P.map f ⧸ (Q.map f).comap (P.map f).subtype) = Module.length R (P ⧸ Q.comap P.subtype) := by
  refine (LinearEquiv.length_eq (Submodule.Quotient.equiv (Q.comap P.subtype) ((Q.map f).comap (P.map f).subtype)
    (Submodule.equivMapOfInjective f hf P) ?_)).symm
  ext ⟨y, hy⟩
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨⟨x, hx⟩, hxQ, hxy⟩
    refine ⟨x, hxQ, ?_⟩
    have := congrArg Subtype.val hxy
    simpa using this
  · rintro ⟨x, hxQ, hxy⟩
    obtain ⟨x', hx', rfl⟩ := hy
    have : x = x' := hf hxy
    subst this
    exact ⟨⟨x, hx'⟩, hxQ, rfl⟩


open scoped _root_.Formalism.L2.Col in
theorem lenUW_map {K : Type} [Field K] [NumberField K] {V V' : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
    (φ : V →ₗ[K] V') (hφ : Function.Injective φ) (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) :
    Formalism.L2.Col.lenUW w (A.map (φ.restrictScalars (𝓞 K))) (B.map (φ.restrictScalars (𝓞 K))) = Formalism.L2.Col.lenUW w A B := by
  unfold Formalism.L2.Col.lenUW Formalism.L2.Col.lenW
  rw [Formalism.L2.Col.atW_map, Formalism.L2.Col.atW_map,
    length_quot_map (φ.restrictScalars (Formalism.L2.Col.Ow w)) hφ]

theorem lat_eq_map (D : D7) (μ : D.what₂.Tup) (j : ℕ) {n : ℕ} (e : (Fin n → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL μ j)
    (N : Submodule (𝓞 D.what₂.LL) (Fin n → D.what₂.LL))
    (hL : OLatTie D.what₂.embLL (D.what₂.MtLat μ j) ((D.what₂.jMt μ j).comp e.toLinearMap) N) :
    lat D μ j = N.map (e.toLinearMap.restrictScalars (𝓞 D.what₂.LL)) := by
  classical
  apply le_antisymm
  · rw [lat, Submodule.span_le]
    intro y hy
    obtain ⟨x, rfl⟩ := e.surjective y
    refine ⟨x, ?_, rfl⟩
    show x ∈ N
    rw [hL.2 x]
    refine ⟨fun v => if v = D.what₂.jMt μ j (e x) then 1 else 0, ?_⟩
    rw [Finset.sum_eq_single (D.what₂.jMt μ j (e x))]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd hy h
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨c, hc⟩ := (hL.2 x).1 hx
    choose! g hg using D.what₂.MtLat_sub μ j
    have hx' : e x = ∑ v ∈ (D.what₂.MtLat μ j).gen, (c v) • g v := by
      apply GlobalTheory.Mem.LiftForms.jMt_injective μ j
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      have hc' : D.what₂.jMt μ j (e x) = ∑ v ∈ (D.what₂.MtLat μ j).gen, D.what₂.embLL (c v : D.what₂.LL) • v := hc
      rw [hc']
      refine Finset.sum_congr rfl fun v hv => ?_
      rw [← algebraMap_smul D.what₂.LL (c v) (g v), map_smulₛₗ, hg v hv]
    show e x ∈ lat D μ j
    rw [hx']
    refine Submodule.sum_mem _ fun v hv => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    show D.what₂.jMt μ j (g v) ∈ (D.what₂.MtLat μ j).gen
    rw [hg v hv]
    exact hv

theorem zRat_and_etaRat_eq : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) (A : FamIn D.what₂.LL G Pl0 T m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin m) (t : T), (Fin (lDim D A P ψ i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (s : ℕ), A.fam.Ok s → ∀ (i : Fin m) (t : T), FormsTie D.what₂.embLL ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lH D A P ψ i t) (lE D A P ψ i t) (D.what₂.eMt (tup t) ((i : ℕ) + 1)) → OLatTie D.what₂.embLL (D.what₂.MtLat (tup t) ((i : ℕ) + 1)) ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lNab D A P ψ i t) → Idx.Z0 D (tup t) ((i : ℕ) + 1) = Submodule.span ℂ (Set.range fun k => (D.what₂.jMt (tup t) ((i : ℕ) + 1)) (eMt i t ((lZ0 D A P ψ Zs i t).mulVec (Pi.single k 1)))) → ZRat D (tup t) ((i : ℕ) + 1) ∧ ∀ w, etaRat D (tup t) ((i : ℕ) + 1) w = A.fam.etaJ P ψ Zs i t (D.plEq w) := by
  intro D G _ _ Pl0 T m A P ψ Zs tup eMt s hOk i t hF hL hZ
  obtain ⟨hinj, hrange, hproj⟩ := _root_.GlobalTheory.EtaJoin.concreteProj_orth D G Pl0 T m A P ψ Zs tup eMt s hOk i t hF hZ
  have hB : BlockHyp (A.fam.L i t) (A.fam.lvlA P ψ) A.v0 s := ⟨hOk.conj, hOk.irr, hOk.lifts i t⟩
  have hcut := BlockDat.lf_cut_nab (Z := Zs.Zl i t) hB
  have hlat := lat_eq_map D (tup t) ((i : ℕ) + 1) (eMt i t) _ hL
  set e := eMt i t with he
  set ψL := (e.toLinearMap ∘ₗ (lZ0 D A P ψ Zs i t).mulVecLin) with hψL
  set R := ratSub D (tup t) ((i : ℕ) + 1) (Idx.Z0 D (tup t) ((i : ℕ) + 1)) with hR
  set Rp := ratSub D (tup t) ((i : ℕ) + 1) (Idx.Z0 D (tup t) ((i : ℕ) + 1))ᗮ with hRp
  have hbot : ∀ y, y ∈ R → y ∈ Rp → y = 0 := by
    intro y h1 h2
    apply GlobalTheory.Mem.LiftForms.jMt_injective (tup t) ((i : ℕ) + 1)
    rw [map_zero]
    have h3 : D.what₂.jMt (tup t) ((i : ℕ) + 1) y ∈ Idx.Z0 D (tup t) ((i : ℕ) + 1) ⊓ (Idx.Z0 D (tup t) ((i : ℕ) + 1))ᗮ :=
      ⟨h1, h2⟩
    rw [Submodule.inf_orthogonal_eq_bot] at h3
    exact h3
  have hmemR : ∀ z, ψL z ∈ R := fun z => by rw [hrange]; exact LinearMap.mem_range_self _ z
  have hup : up D (tup t) ((i : ℕ) + 1) =
      ((A.fam.L i t).Tl (A.fam.lvlA P ψ) (Zs.Zl i t)).map (ψL.restrictScalars (𝓞 D.what₂.LL)) := by
    ext y
    constructor
    · rintro ⟨hyR, hy⟩
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hy
      rw [hlat] at ha
      obtain ⟨x, hx, rfl⟩ := ha
      have hd : y - ψL ((lPrj D A P ψ Zs i t).mulVec x) = 0 := by
        apply hbot
        · exact R.sub_mem hyR (hmemR _)
        · have : y - ψL ((lPrj D A P ψ Zs i t).mulVec x) = (e x - ψL ((lPrj D A P ψ Zs i t).mulVec x)) + b := by
            rw [← hab]
            simp only [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
            abel
          rw [this]
          exact Rp.add_mem (hproj x) hb
      refine ⟨(lPrj D A P ψ Zs i t).mulVec x, ⟨x, hx, rfl⟩, ?_⟩
      show ψL _ = y
      exact (sub_eq_zero.1 hd).symm
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨hmemR _, Submodule.mem_sup.2 ⟨e x, ?_, ψL ((lPrj D A P ψ Zs i t).mulVec x) - e x, ?_, ?_⟩⟩
      · rw [hlat]
        exact ⟨x, hx, rfl⟩
      · show _ ∈ Rp
        rw [← neg_sub]
        exact Rp.neg_mem (hproj x)
      · show e x + (ψL ((lPrj D A P ψ Zs i t).mulVec x) - e x) = ψL ((lPrj D A P ψ Zs i t).mulVec x)
        abel
  have hlow : low D (tup t) ((i : ℕ) + 1) =
      ((A.fam.L i t).cutZ (A.fam.lvlA P ψ) (Zs.Zl i t)).map (ψL.restrictScalars (𝓞 D.what₂.LL)) := by
    ext y
    constructor
    · rintro ⟨hy, hyR⟩
      have hyR' : y ∈ R := hyR
      rw [hrange] at hyR'
      obtain ⟨z, rfl⟩ := hyR'
      rw [hlat] at hy
      obtain ⟨x, hx, hxz⟩ := hy
      have hxz' : x = (lZ0 D A P ψ Zs i t).mulVec z := e.injective hxz
      refine ⟨z, ?_, rfl⟩
      rw [← hcut]
      show (lZ0 D A P ψ Zs i t).mulVec z ∈ lNab D A P ψ i t
      rw [← hxz']
      exact hx
    · rintro ⟨z, hz, rfl⟩
      refine ⟨?_, hmemR z⟩
      rw [hlat]
      rw [← hcut] at hz
      exact ⟨(lZ0 D A P ψ Zs i t).mulVec z, hz, rfl⟩
  refine ⟨?_, fun w => ?_⟩
  · rw [ZRat, eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := e.surjective y
    refine Submodule.mem_sup.2 ⟨ψL ((lPrj D A P ψ Zs i t).mulVec x), hmemR _, e x - ψL ((lPrj D A P ψ Zs i t).mulVec x),
      hproj x, ?_⟩
    abel
  · rw [etaRat, hup, hlow, lenUW_map ψL hinj]
    rfl

end GlobalTheory.EtaJoin.Side
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehLanglandsQuotient
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

noncomputable section

namespace GlobalTheory.LocGL

theorem IsLSeg.nu_rep {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {δ : IrrGL (k := k)} {Δ : Segment k} (h : IsLSeg Δ δ.rep) (c : ℂ) : IsLSeg (Δ.nu c) (δ.nu c).rep :=
  (h.tw (absPow k c) (isSmoothChar_absPow c)).of_equiv (δ.twEquiv _ _)

theorem IsSpeh.nu_rep {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {δ x : IrrGL (k := k)} {m : ℕ} (h : IsSpeh δ m x.rep) (s : ℂ) : IsSpeh (δ.nu s) m (x.nu s).rep := by
  obtain ⟨hd, h'⟩ := h.tw (absPow k s) (isSmoothChar_absPow s)
  exact ⟨hd, h'.of_equiv (x.twEquiv _ _) (.refl _)⟩

theorem isL_speh_nu (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hP : ∀ (δ δ' : IrrGL (k := k)) (Δ Δ' : Segment k), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsLSeg Δ' δ'.rep →
      IsUnitarisable δ'.rep → ∀ x y : ℝ, (Δ.nu x).Precedes (Δ'.nu y) → x + 1 ≤ y) :
    ∀ (δ x : IrrGL (k := k)) (Δ : Segment k) (m : ℕ), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsSpeh δ m x.rep →
      ∀ s : ℝ, IsL ↑(List.ofFn fun i : Fin m => Δ.nu ((s + ((m : ℝ) - 1) / 2 - (i : ℕ) : ℝ) : ℂ)) (x.nu (s : ℂ)).rep := by
  intro δ x Δ m hL hU hS s
  obtain ⟨hd, hc⟩ := hS.nu_rep (s : ℂ)
  set c : Fin m → ℝ := fun i => s + ((m : ℝ) - 1) / 2 - (i : ℕ) with hcdef
  have hy : ∀ i, spehFactor (δ.nu s) m i = δ.nu (c i : ℂ) := fun i => by
    simp only [spehFactor, IrrGL.nu_nu, hcdef]
    congr 1
    push_cast
    ring
  refine ⟨m, spehFactor (δ.nu s) m, hd, ⟨fun i => Δ.nu (c i : ℂ), ⟨?_, ?_⟩, ?_⟩, hc⟩
  · rw [Fin.univ_val_map]
  · intro i j hij hp
    have h1 := hP δ δ Δ Δ hL hU hL hU (c i) (c j) hp
    have h2 : ((i : ℕ) : ℝ) < (j : ℕ) := by exact_mod_cast hij
    simp only [hcdef] at h1
    linarith
  · intro i
    rw [hy i]
    exact hL.nu_rep _

end GlobalTheory.LocGL
end
end

