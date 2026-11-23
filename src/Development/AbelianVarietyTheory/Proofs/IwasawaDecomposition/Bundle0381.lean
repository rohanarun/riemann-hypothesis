module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1110
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0062
public import Formalism.LocalToGlobal.Columns.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousActP
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0207
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0377
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0373
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionIsoTame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0011
public import Formalism.LocalToGlobal.Columns.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesStdMatched
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0310

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGoodCharacterSetIdempotentCoeffCoefficient
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.GoodSetExists

section Gen

variable {G : Type} [Group G] [Fintype G]

theorem one_ne_zero_of_mem (ψ : G → ℂ) (h : ψ ∈ Formalism.L2.Col.gxIrrSet (G := G) ℂ) : ψ 1 ≠ 0 := by
  obtain ⟨n, ρ, hρ, rfl⟩ := h
  intro e
  rw [Representation.char_one, Nat.cast_eq_zero, Module.finrank_zero_iff] at e
  exact (bot_ne_top (α := Subrepresentation ρ)) (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

theorem coeff_conj_of_center {e : MonoidAlgebra ℂ G} (he : e ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G)) (x y : G) :
    e.coeff (y * x * y⁻¹) = e.coeff x := by
  have h := congrArg (fun a : MonoidAlgebra ℂ G => a.coeff (y * x))
    ((Subalgebra.mem_center_iff.1 he (MonoidAlgebra.single y 1)).symm)
  simp only [MonoidAlgebra.coeff_mul_single_apply, MonoidAlgebra.coeff_single_mul_apply, mul_one, one_mul,
    inv_mul_cancel_left] at h
  exact h

end Gen

section Record

variable (X : Stages) (px : PreX X.B.toPre)

theorem exists_goodSet_Ks (eR : Gc X.B px ≃* G0g X.toD7.nd) :
    ∃ Xg : Finset (Gc X.B px → X.B.LL), GoodSet X (px := px) eR Xg ∧ ∀ g, (idemOf Xg).coeff g ∈ X.B.Ks := by
  classical
  let σ := X.B.embLL
  let f := MonoidAlgebra.domCongr ℂ ℂ eR.symm
  let e : MonoidAlgebra ℂ (Gc X.B px) := f X.toD7.ntypes.e0
  have hcoeff : ∀ g, e.coeff g = X.toD7.ntypes.e0.coeff (eR g) := fun g => by
    simp [e, f, MonoidAlgebra.domCongr_apply]
  obtain ⟨hcen0, hid0⟩ := GlobalTheory.GoodLatCompare.goodSeriesIdempotent_central_idempotent X.toD7
  have hid : e * e = e := by simp only [e, ← map_mul, hid0]
  have hcen : e ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (Gc X.B px)) := by
    refine Subalgebra.mem_center_iff.2 fun b => ?_
    obtain ⟨c, rfl⟩ := f.surjective b
    simp only [e, ← map_mul, (Subalgebra.mem_center_iff.1 hcen0 c)]
  have hcard : Fintype.card (Gc X.B px) = X.B.restRowsFiniteGroupCard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr eR.toEquiv]
    have : ∀ k, NeZero (X.toD7.host.g k) := fun k => ⟨(X.toD7.host.g_prime k).ne_zero⟩
    rw [Nat.card_pi, Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    change ∏ _y : X.toD7.nd.PlG k, Nat.card (GL (Fin X.toD7.R.r) (ZMod (X.toD7.host.g k))) = _
    rw [Finset.prod_const, Finset.card_univ, X.toD7.nd.card_PlG k]
    rfl
  obtain ⟨z, hzK, hz⟩ := X.B.roots_Ks X.B.restRowsFiniteGroupCard (by simp)
  have hzp : IsPrimitiveRoot z (Fintype.card (Gc X.B px)) := by
    rw [hcard, ← IsPrimitiveRoot.map_iff_of_injective σ.injective]
    rw [show σ z = _ from hz]
    exact Complex.isPrimitiveRoot_exp _ X.B.restRowsFiniteGroupCard_pos.ne'
  refine ⟨Formalism.L2.Col.XgE σ e, Model.goodSet_of_idem X eR _ Formalism.L2.Col.XgE_irr fun g => ?_, fun g => ?_⟩
  · let A := (Formalism.L2.Col.gxIrrSet_finite (G := Gc X.B px) (k := ℂ)).toFinset
    have hA : ∀ ψ, ψ ∈ A ↔ ψ ∈ Formalism.L2.Col.gxIrrSet (G := Gc X.B px) ℂ := fun ψ => Set.Finite.mem_toFinset _
    have hexp := _root_.GlobalTheory.IdemExpand.eq_idemOf_filter A e (fun ψ hψ => one_ne_zero_of_mem ψ ((hA ψ).1 hψ)) (GlobalTheory.T.sum_irrChar_one_mul_irrChar_column_orthogonality A hA)
      (fun ψ hψ x => GlobalTheory.T.classFunction_acts_by_scalar_on_irrChar e (coeff_conj_of_center hcen) ψ ((hA ψ).1 hψ) x) hid
    have himg : (A.filter fun ψ => ∑ g, e.coeff g * ψ g = ψ 1) =
        (Formalism.L2.Col.XgE σ e).image (fun χ g => σ (χ g)) := by
      ext ψ
      simp only [Finset.mem_filter, Finset.mem_image, hA, Formalism.L2.Col.mem_XgE]
      constructor
      · rintro ⟨hψ, hs⟩
        obtain ⟨χ, hχ, hχψ⟩ := GlobalTheory.T.absIrrChar_realise_of_primitiveRoot_card σ z hzp ψ hψ
        refine ⟨χ, ⟨hχ, ?_⟩, funext hχψ⟩
        simp only [hχψ]
        exact hs
      · rintro ⟨χ, ⟨hχ, hs⟩, rfl⟩
        exact ⟨GlobalTheory.T.absIrrChar_comp_mem_complexIrrCharSet σ χ hχ, hs⟩
    have hinj : Set.InjOn (fun (χ : Gc X.B px → X.B.LL) g => σ (χ g)) (Formalism.L2.Col.XgE σ e : Set _) :=
      fun χ _ χ' _ h => funext fun g => σ.injective (congrFun h g)
    rw [← hcoeff g]
    conv_rhs => rw [hexp]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [himg, coeff_idemOf, coeff_idemOf, Finset.sum_image hinj, map_sum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    simp [σ, map_div₀, map_mul, map_natCast]
  · rw [coeff_idemOf]
    have hcl : ∀ y ∈ Subring.closure ({z} : Set X.B.LL), y ∈ X.B.Ks := fun y hy => by
      have : Subring.closure ({z} : Set X.B.LL) ≤ X.B.Ks.toSubfield.toSubring := by
        rw [Subring.closure_le, Set.singleton_subset_iff]
        exact hzK
      exact this hy
    refine IntermediateField.sum_mem _ fun χ hχ => ?_
    have hχ' := Formalism.L2.Col.XgE_irr χ hχ
    exact IntermediateField.mul_mem _ (IntermediateField.div_mem _ (hcl _ (GlobalTheory.T.absIrrChar_mem_closure_primitiveRoot_card z hzp χ hχ' 1))
      (IntermediateField.natCast_mem _ _)) (hcl _ (GlobalTheory.T.absIrrChar_mem_closure_primitiveRoot_card z hzp χ hχ' _))

end Record

end GlobalTheory.Mem.R3.GoodSetExists

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsomVec
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.GsdIso

open _root_.Formalism.L2.Col Formalism.IndefR.Bridge

theorem exists_isom_vec : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] (S : Formalism.L2.Col.GSD K) (ok : S.Ok) {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ι : Γ →* G) (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (P : Bridge.ClassPres ι (S.toCSD ok) σ ρ J χ) (c : S.V →ₛₗ[σ] W) (d : G → S.D),
  (∀ (φ : S.EqFun) (h : G), P.extL (S.res ok φ) h = c (φ.1 (d h))) → (∃ φ : S.EqFun, φ ≠ 0) → ∃ v : S.V, c v ≠ 0 ∧ inner ℂ (c v) (c v) = σ (S.pair v v) := by
  classical
  intro K _ _ _ S ok G Γ W _ _ _ _ ι σ ρ J χ P c d H hne
  obtain ⟨φ, hφ⟩ := hne
  obtain ⟨k, hk⟩ : ∃ k, φ.1 (S.outSec.rep k) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφ ((S.res ok).map_eq_zero_iff.1 (Subtype.ext (funext h)))
  set x := φ.1 (S.outSec.rep k) with hx
  have vi := (S.res ok φ).2 k
  let f : (S.toCSD ok).Forms := ⟨Pi.single k x, fun c' γ => by
    by_cases h : c' = k
    · subst h
      rw [Pi.single_eq_same]
      exact vi γ
    · rw [Pi.single_eq_of_ne h, map_zero]⟩
  have H1 := H ((S.res ok).symm f) (P.y k)
  rw [ClassPres.extL_apply, LinearEquiv.apply_symm_apply, GlobalTheory.PresBasic.ext_y] at H1
  have e2 : ((S.res ok).symm f).1 (d (P.y k)) =
      S.ρ (S.outSec.mv (d (P.y k))) ((Pi.single k x : S.Cl → S.V) (S.cls (d (P.y k)))) := rfl
  rw [e2] at H1
  have hfk : ((f : S.Cl → S.V)) k = x := by simp [f]
  rw [hfk] at H1
  have hc0 : P.coef x ≠ 0 := fun h => hk (GlobalTheory.PresBasic.coef_injective P (h.trans (map_zero _).symm))
  have hc : S.cls (d (P.y k)) = k := by
    by_contra h
    rw [Pi.single_eq_of_ne h, map_zero, map_zero] at H1
    exact hc0 H1
  rw [hc, Pi.single_eq_same] at H1
  refine ⟨S.ρ (S.outSec.mv (d (P.y k))) x, H1 ▸ hc0, ?_⟩
  rw [← H1, P.coef_pair, ok.inv]

end GlobalTheory.Mem.GsdIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevOfAll
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MtIn.LevAll

theorem exists_levOf_all : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px), I.Ok → SelHalf I → ∀ (U₀ : Set I.ι) (L₀ : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U₀)), LevOf X I U₀ L₀ → ∀ U : Set I.ι, ∃ L, LevOf X I U L := by
  intro X px I hI hsel U₀ L₀ hL₀ U
  classical
  have htw : ∀ a, Chr.IsTwist X.B.host I.S (I.xi a) := fun a =>
    (GlobalTheory.Mem.ReadTwist.isTwist_of_reads _ X.B.host _ _ _ (I.tup a) (I.xi a) (hI.xi_reads a)).1
  have hram := GlobalTheory.Mem.Col2.RamQ.ram_iff X px I hI
  have hQr : ∀ a, ∀ PP ∈ I.Q a, ¬ (I.xi a).UnrAt PP := fun a PP h => (hram a PP).2 (Or.inl h)
  have hpl := fun a => GlobalTheory.Mem.TwistPlaces.twistPlaces X px I hI a (hQr a)
  obtain ⟨L0, h1, h2, h3, -, h4⟩ := GlobalTheory.LevelChoices.exists_levCh X.toD7 (Top.Fr.at X I.C) (TupU I U)
    (mu0F (X := X.B.fields) (tuOf I U)) (fun t => I.xi (ixOf I U t)) (fun t => I.Q (ixOf I U t))
    (hI.xi_inj.comp (ixOf_injective I U)) (by simp only [ixOf_mu0F]; exact hI.trueColumnChoices_heckeChar_reference_eq_one)
    (fun t => (htw _).1) (fun t => (htw _).2.1) (fun t => (htw _).2.2.1)
    (fun t => (hpl _).1) (fun t => (hpl _).2)
    (fun p hp => by
      have hpp : p.Prime := by
        rcases hp with rfl | rfl
        exacts [X.B.host.pde_prime, X.B.host.pde'_prime]
      obtain ⟨𝔭, h𝔭⟩ := GlobalTheory.Mem.R3.Model.exists_under_of_selHalf I hsel p hpp
      exact ⟨𝔭, fun t PP hPP hp' => h𝔭 _ PP hPP hp'⟩)
    (fun t PP => hram _ PP)
  have hPg : L0.Pg = (X.B.primes px).vGs := by
    refine Finset.ext fun P => (h4.Pg P).trans ?_
    rw [h1]
    exact (GlobalTheory.Mem.R3.Model.mem_vGs_iff I hI P).symm
  let L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U) :=
    { L0 with
      ΛY := L₀.ΛY
      ΛW := L₀.ΛW
      ΛX := L₀.ΛX
      ΛV := L₀.ΛV
      βY := L₀.βY
      βW := L₀.βW
      βX := L₀.βX
      βV := L₀.βV }
  exact ⟨L, ⟨⟨h4.mu0, h4.eta, h4.xi, h4.xi_inj, h4.xi_base, h4.xi_fin, h4.xi_triv, h4.xi_tame, h4.Pg, h4.Q_pl,
      h4.Q_off, h4.Q_de, h4.Q_ram, h4.chi, h4.xiR, hL₀.is.βY, hL₀.is.βX, hL₀.is.βV, hL₀.is.βW⟩, h1, fun t => congrFun h2 t, hPg,
      fun t => congrFun h3 t, hL₀.beta⟩⟩

end GlobalTheory.MtIn.LevAll

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSplitPlaceComponentHeckeCharResidue
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.XiRes

theorem exists_isCompAt_res : ∀ (D : D7) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (φ : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* kP s.w), Function.Surjective φ → (∀ x, φ x = 0 ↔ Valued.v (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) < 1) → (∀ a : 𝓞 D.host.E, ∃ h : s.i (a : D.host.E) ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E), φ ⟨_, h⟩ = Ideal.Quotient.mk _ a) → ∀ (χ : HChar D.host.E) (c : (kP s.w)ˣ →* ℂˣ), IsRes χ s.w c → ∃ ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ, NG.IsCompAt χ s ξ ∧ ∀ (u : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ) (x : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) (w : (kP s.w)ˣ), (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) = u → φ x = w → ξ u = c w := by
  intro D s φ _hφ hker hres χ c hc
  obtain ⟨e, hec, -, hei⟩ := GlobalTheory.SplitCompl.exists_ringEquiv D.host.E s
  have htame : χ.TameAt s.w := GlobalTheory.ChainOnto.TameRes.tameAt_of_isRes D χ s.w c hc
  let ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ :=
    (χ.loc s.w).comp (Units.map e.toRingHom.toMonoidHom)
  have hlt : WithZero.exp (-((1 : ℕ) : ℤ)) < 1 := by
    rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.mpr (by norm_num)

  have h1 : ∀ u : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ,
      Valued.v ((u : s.v.adicCompletion (maximalRealSubfield D.host.E)) - 1) < 1 → ξ u = 1 := by
    intro u hu
    have hu' : Valued.v (e u - 1) < 1 := by
      have := (GlobalTheory.TypeBlockFix.v_map_lt_one_iff _ _ e hec _).2 hu
      rwa [map_sub, map_one] at this
    refine htame (Units.map e.toRingHom.toMonoidHom u) ?_ ?_
    · show Valued.v (e u) = 1
      have := Valuation.map_one_add_of_lt _ hu'
      rwa [add_sub_cancel] at this
    · show Valued.v (e u - 1) ≤ WithZero.exp (-((1 : ℕ) : ℤ))
      rcases eq_or_ne (Valued.v (e u - 1)) 0 with h0 | h0
      · rw [h0]; exact zero_le'
      · rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hu'
        rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
        push_cast; omega
  have h2 : ∀ k : D.host.Eˣ, ξ (Units.map (s.i : D.host.E →* s.v.adicCompletion (maximalRealSubfield D.host.E)) k) =
      χ.locK s.w k := by
    intro k
    show χ.loc s.w _ = χ.loc s.w _
    congr 1
    apply Units.ext
    exact hei k
  refine ⟨ξ, ⟨⟨1, fun u hu => h1 u (lt_of_le_of_lt hu hlt)⟩, h2⟩, ?_⟩
  intro u x w hxu hxw
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := s.w.asIdeal) (w : kP s.w)
  obtain ⟨hai, hφa⟩ := hres a
  haveI : s.w.asIdeal.IsMaximal := s.w.isMaximal
  haveI : Nontrivial (kP s.w) := Ideal.Quotient.nontrivial_iff.2 s.w.isPrime.ne_top
  have hw0 : (w : kP s.w) ≠ 0 := w.ne_zero
  have hva : Valued.v (s.i (a : D.host.E)) = 1 := by
    refine le_antisymm hai (not_lt.1 fun h => hw0 ?_)
    rw [← ha, ← hφa]; exact (hker ⟨_, hai⟩).2 h
  have ha0 : (a : D.host.E) ≠ 0 := by
    intro h0; rw [h0, map_zero, map_zero] at hva; exact zero_ne_one hva
  have hdiff : Valued.v ((u : s.v.adicCompletion (maximalRealSubfield D.host.E)) - s.i (a : D.host.E)) < 1 := by
    have := (hker (x - ⟨_, hai⟩)).1 (by rw [map_sub, hxw, hφa, ha, sub_self])
    rw [← hxu]; exact this
  let ka : D.host.Eˣ := Units.mk0 _ ha0
  let ua := Units.map (s.i : D.host.E →* s.v.adicCompletion (maximalRealSubfield D.host.E)) ka
  have hua : (ua : s.v.adicCompletion (maximalRealSubfield D.host.E)) = s.i (a : D.host.E) := rfl
  have h3 : ξ (u * ua⁻¹) = 1 := by
    apply h1
    have : ((u * ua⁻¹ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ) : s.v.adicCompletion (maximalRealSubfield D.host.E)) - 1 =
        ((u : s.v.adicCompletion (maximalRealSubfield D.host.E)) - ua) * (ua : s.v.adicCompletion (maximalRealSubfield D.host.E))⁻¹ := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, sub_mul, mul_inv_cancel₀ ua.ne_zero]
    rw [this, map_mul, map_inv₀, hua, hva, inv_one, mul_one]
    exact hdiff
  have h4 : c w = χ.locK s.w ka := hc a ka w rfl ha.symm
  rw [map_mul, map_inv, mul_inv_eq_one] at h3
  rw [h3, h4]
  exact h2 ka

end GlobalTheory.XiRes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryGroupsEquivUnitFormGramOne
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

namespace GlobalTheory.Mem.R3.LiftBrg.StdGroups

theorem castGL_bc {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {m n : ℕ} (h : m = n) (x : GL (Fin m) A) :
    castGL h (Formalism.UG.bc f x) = Formalism.UG.bc f (castGL h x) := by
  subst h
  ext i j
  simp [castGL, Formalism.UG.bc, Matrix.reindexAlgEquiv_apply]

theorem castGL_symm_castGL' {A : Type} [CommRing A] {m n : ℕ} (h : m = n) (x : GL (Fin m) A) :
    castGL h.symm (castGL h x) = x := by
  subst h
  ext i j
  simp [castGL, Matrix.reindexAlgEquiv_apply]

theorem castGL_mem_UJ_one {A : Type} [CommRing A] (σ : A →+* A) {m n : ℕ} (h : m = n) (x : GL (Fin m) A)
    (hx : x ∈ Formalism.UG.UJ σ (1 : Matrix (Fin m) (Fin m) A)) : castGL h x ∈ Formalism.UG.UJ σ (1 : Matrix (Fin n) (Fin n) A) := by
  subst h
  have e : castGL (rfl : m = m) x = x := by
    ext i j
    simp [castGL, Matrix.reindexAlgEquiv_apply]
  rwa [e]

theorem bc_injective {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Injective f) {m : ℕ} :
    Function.Injective (Formalism.UG.bc (n := Fin m) f) := by
  intro x y hxy
  ext i j
  exact hf (congrArg (fun z : GL (Fin m) B => (z : Matrix (Fin m) (Fin m) B) i j) hxy)

def phiG (X : Stages) (i : Fin X.toD7.R.m) (hg : (Vc X.toD7 i).gram = 1) :
    Bridge.Gf (Vc X.toD7 i) →* Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV where
  toFun g := ⟨castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) g.1), by
    obtain ⟨k, hk⟩ := g.2
    have h1 : Formalism.UG.bc (swapAE X.toD7) g.1 ∈ Formalism.L2.DIV.UA X.toD7.sp.cm (Vc X.toD7 i).gram := by
      rw [← hk]
      exact GlobalTheory.LevSplit.finE_mem_UA _ k
    rw [hg] at h1
    exact castGL_mem_UA_std _ _ _ h1⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)

theorem phiG_val (X : Stages) (i : Fin X.toD7.R.m) (hg : (Vc X.toD7 i).gram = 1) (g : Bridge.Gf (Vc X.toD7 i)) :
    (phiG X i hg g : GL (Fin X.B.R.nV) (LiftBrg.EA X)) = castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) g.1) := rfl

theorem phiG_injective (X : Stages) (i : Fin X.toD7.R.m) (hg : (Vc X.toD7 i).gram = 1) :
    Function.Injective (phiG X i hg) := by
  intro a b hab
  have h1 := congrArg (fun z : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV => (z : GL (Fin X.B.R.nV) (LiftBrg.EA X))) hab
  simp only [phiG_val] at h1
  have h2 := (castGL (rkEq X i).symm).injective h1
  exact Subtype.ext (bc_injective _ (Algebra.TensorProduct.comm _ _ _).injective h2)

theorem phiG_surjective (X : Stages) (i : Fin X.toD7.R.m) (hg : (Vc X.toD7 i).gram = 1) :
    Function.Surjective (phiG X i hg) := by
  intro x
  have hy : castGL (rkEq X i) (x : GL (Fin X.B.R.nV) (LiftBrg.EA X)) ∈ Formalism.L2.DIV.UA X.toD7.sp.cm (Vc X.toD7 i).gram := by
    rw [hg]
    exact castGL_mem_UA_std _ _ _ x.2
  refine ⟨⟨finHom (Vc X.toD7 i) (GlobalTheory.StdFrameExist.liftF (Vc X.toD7 i) _ hy), _, rfl⟩, Subtype.ext ?_⟩
  rw [phiG_val]
  have e := GlobalTheory.StdFrameExist.finE_liftF (Vc X.toD7 i) _ hy
  change castGL (rkEq X i).symm (finE (Vc X.toD7 i) (GlobalTheory.StdFrameExist.liftF (Vc X.toD7 i) _ hy)) = _
  rw [e, castGL_symm_castGL']

end GlobalTheory.Mem.R3.LiftBrg.StdGroups

namespace GlobalTheory.Mem.R3.LiftBrg.StdGroups

theorem bc_inclR_mem_HR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {m : ℕ} (J : Matrix (Fin m) (Fin m) E) (γ : GL (Fin m) E) (hγ : γ ∈ Formalism.UG.UJ (σ : E →+* E) J) :
    Formalism.UG.bc (inclR (F := F) R) γ ∈ HR R σ J := by
  have h : Formalism.UG.cT (σ : E →+* E) (γ : Matrix (Fin m) (Fin m) E) * J * γ = J := hγ
  show Formalism.UG.cT (sigR R σ) ((γ : Matrix (Fin m) (Fin m) E).map (inclR R)) * J.map (inclR R) *
    (γ : Matrix (Fin m) (Fin m) E).map (inclR R) = J.map (inclR R)
  have h2 : Formalism.UG.cT (sigR R σ) ((γ : Matrix (Fin m) (Fin m) E).map (inclR R)) =
      (Formalism.UG.cT (σ : E →+* E) (γ : Matrix (Fin m) (Fin m) E)).map (inclR (F := F) R) := by
    ext i j
    simp [Formalism.UG.cT, sigR, inclR]
  rw [h2, ← Matrix.map_mul, ← Matrix.map_mul, h]

def psiQ (X : Stages) (i : Fin X.toD7.R.m) (hg : (Vc X.toD7 i).gram = 1) :
    Formalism.L2.Col.URat X.toD7.sp.cm X.B.R.nV →* GQ (Vc X.toD7 i) where
  toFun γ :=
    have hm : castGL (rkEq X i) (γ : GL (Fin X.B.R.nV) X.toD7.host.E) ∈
        Formalism.UG.UJ (X.toD7.sp.cm.sig : X.toD7.host.E →+* X.toD7.host.E) (Vc X.toD7 i).gram := by
      rw [hg]
      exact castGL_mem_UJ_one _ _ _ γ.2
    ⟨(show GA X.toD7 (Vc X.toD7 i) from
        (⟨Formalism.UG.bc (inclR (F := X.toD7.host.F) (AF X.toD7.host.F)) (castGL (rkEq X i) (γ : GL (Fin X.B.R.nV) X.toD7.host.E)),
          bc_inclR_mem_HR _ _ _ _ hm⟩ : HR (AF X.toD7.host.F) X.toD7.sp.cm.sig (Vc X.toD7 i).gram)),
      Subgroup.mem_subgroupOf.2 ⟨_, hm, rfl⟩⟩
  map_one' := Subtype.ext (Subtype.ext (by first | rfl | (simp only [map_one]; rfl) | (simp <;> rfl)))
  map_mul' a b := Subtype.ext (Subtype.ext (by first | rfl | (simp only [map_mul]; rfl) | (simp <;> rfl)))

theorem psiQ_mat (X : Stages) (i : Fin X.toD7.R.m) (hg : (Vc X.toD7 i).gram = 1) (γ : Formalism.L2.Col.URat X.toD7.sp.cm X.B.R.nV) :
    matHom (Vc X.toD7 i) (psiQ X i hg γ : GA X.toD7 (Vc X.toD7 i)) =
      Formalism.UG.bc (incA X.toD7) (castGL (rkEq X i) (γ : GL (Fin X.B.R.nV) X.toD7.host.E)) := rfl

theorem phiG_ratF_psiQ (X : Stages) (i : Fin X.toD7.R.m) (hg : (Vc X.toD7 i).gram = 1) (γ : Formalism.L2.Col.URat X.toD7.sp.cm X.B.R.nV) :
    phiG X i hg (Bridge.ratF (Vc X.toD7 i) (psiQ X i hg γ)) = Formalism.L2.Col.ratIn X.toD7.sp.cm X.B.R.nV γ := by
  apply Subtype.ext
  rw [phiG_val, Formalism.L2.Col.ratIn_val]
  have e1 : ((Bridge.ratF (Vc X.toD7 i) (psiQ X i hg γ)) : GL (Fin (Vc X.toD7 i).rank) _) =
      Formalism.UG.bc (inclR (F := X.toD7.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F)) (castGL (rkEq X i) (γ : GL (Fin X.B.R.nV) X.toD7.host.E)) := by
    change finHom (Vc X.toD7 i) _ = _
    rw [finHom, MonoidHom.comp_apply, Subgroup.coe_subtype, psiQ_mat]
    exact GlobalTheory.HLatMove.bc_map_bc_inclR _ _
  rw [e1]
  have e2 : Formalism.UG.bc (swapAE X.toD7) (Formalism.UG.bc (inclR (F := X.toD7.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F))
      (castGL (rkEq X i) (γ : GL (Fin X.B.R.nV) X.toD7.host.E))) =
      Formalism.UG.bc (Formalism.L2.Col.iA X.toD7.host.F X.toD7.host.E) (castGL (rkEq X i) (γ : GL (Fin X.B.R.nV) X.toD7.host.E)) := by
    ext a b
    simp [Formalism.UG.bc, swapAE, inclR, Formalism.UG.inclE]
  rw [e2, ← castGL_bc, castGL_symm_castGL']

theorem psiQ_injective (X : Stages) (i : Fin X.toD7.R.m) (hg : (Vc X.toD7 i).gram = 1) :
    Function.Injective (psiQ X i hg) := by
  intro a b hab
  have h1 : Formalism.L2.Col.ratIn X.toD7.sp.cm X.B.R.nV a = Formalism.L2.Col.ratIn X.toD7.sp.cm X.B.R.nV b := by
    rw [← phiG_ratF_psiQ X i hg a, ← phiG_ratF_psiQ X i hg b, hab]
  have h2 := congrArg (fun z : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV => (z : GL (Fin X.B.R.nV) (LiftBrg.EA X))) h1
  simp only [Formalism.L2.Col.ratIn_val] at h2
  exact Subtype.ext (Formalism.L2.DIV.incl_inj _ _ _ h2)

theorem psiQ_surjective (X : Stages) (i : Fin X.toD7.R.m) (hg : (Vc X.toD7 i).gram = 1) :
    Function.Surjective (psiQ X i hg) := by
  intro δ
  obtain ⟨γE, hγE, e⟩ := Subgroup.mem_subgroupOf.1 δ.2
  have hγ : castGL (rkEq X i).symm γE ∈ Formalism.L2.Col.URat X.toD7.sp.cm X.B.R.nV := by
    rw [hg] at hγE
    exact castGL_mem_UJ_one _ _ _ hγE
  refine ⟨⟨_, hγ⟩, Subtype.ext (Subtype.ext ?_)⟩
  change Formalism.UG.bc (inclR (F := X.toD7.host.F) (AF X.toD7.host.F)) (castGL (rkEq X i) (castGL (rkEq X i).symm γE)) = _
  rw [castGL_symm_castGL' (rkEq X i).symm γE]
  exact e

theorem stdGroups_equiv : ∀ (X : Stages) (i : Fin X.toD7.R.m), (Vc X.toD7 i).gram = 1 →
    ∃ (eG : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV ≃* Bridge.Gf (Vc X.toD7 i))
      (eΓ : Formalism.L2.Col.URat X.toD7.sp.cm X.B.R.nV ≃* GQ (Vc X.toD7 i)),
      (∀ x, LiftBrg.castGL (LiftBrg.rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7)
          ((eG x : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F ⊗[X.toD7.host.F] X.toD7.host.E))) =
        (x : GL (Fin X.B.R.nV) (LiftBrg.EA X))) ∧
      (∀ γ, Bridge.ratF (Vc X.toD7 i) (eΓ γ) = eG (Formalism.L2.Col.ratIn X.toD7.sp.cm X.B.R.nV γ)) ∧
      (∀ γ, Bridge.IsRatMat (Vc X.toD7 i) (eΓ γ) (LiftBrg.castGL (LiftBrg.rkEq X i) (γ : GL (Fin X.B.R.nV) X.toD7.host.E))) := by
  intro X i hg
  let eG0 := MulEquiv.ofBijective (phiG X i hg) ⟨phiG_injective X i hg, phiG_surjective X i hg⟩
  let eQ := MulEquiv.ofBijective (psiQ X i hg) ⟨psiQ_injective X i hg, psiQ_surjective X i hg⟩
  refine ⟨eG0.symm, eQ, fun x => ?_, fun γ => ?_, fun γ => ?_⟩
  · have h := eG0.apply_symm_apply x
    exact congrArg (fun z : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV => (z : GL (Fin X.B.R.nV) (LiftBrg.EA X))) h
  · rw [MulEquiv.eq_symm_apply]
    exact phiG_ratF_psiQ X i hg γ
  · exact psiQ_mat X i hg γ

end GlobalTheory.Mem.R3.LiftBrg.StdGroups
end
end

