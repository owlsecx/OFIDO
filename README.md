# 🦉 OFIDO

<p align="center">
  <img src="https://img.shields.io/badge/Platform-Linux-0a0c10?style=flat-square"/>
  <img src="https://img.shields.io/badge/Category-Password%20/%20Auth-blue?style=flat-square"/>
  <img src="https://img.shields.io/badge/License-MIT-green?style=flat-square"/>
  <img src="https://img.shields.io/badge/Part%20of-OwlSec%20Toolkit-7b5ea7?style=flat-square"/>
  <img src="https://img.shields.io/badge/Version-1.0-cyan?style=flat-square"/>
</p>

> **OFIDO** — FIDO2/WebAuthn inspector & verifier (signatures, attestation, MDS) ║

---

> ⚠️ **AUTHORISED USE ONLY** — Use only on systems you own or have explicit written permission to test. Unauthorised use is illegal.

---

## 📌 Overview

OFIDO — FIDO2/WebAuthn inspector & verifier (signatures, attestation, MDS). FIDO2 / WebAuthn Inspector & Verifier Verifies WebAuthn ceremonies offline the way a relying party must: clientDataJSON (type, origin, challenge, crossOrigin), rpIdHash, authenticator flags (UP/UV/BE/BS), signCount clone detection, credential COSE keys, and the cryptographic signatures — attestation statements (packed, fido-u2f, apple, android-key, tpm, none) with x5c chain checks against --roots or the FIDO MDS3 blob, and assertion signatures against the stored credential key. Accepts raw CBOR / hex / base64 or a browser's PublicKeyCredential JSON.

---

## ✨ Features

- Inspect FIDO2 / WebAuthn assertions and attestations
- Verify signatures and attestation statement structure
- MDS-oriented checks for authenticator metadata context
- Offline analysis suitable for identity security reviews
- Clear pass/fail reporting with graded posture
- Export verification results for audits

---

## ⚙️ Requirements

- **Linux**
- **Go 1.21+** (stdlib only; `CGO_ENABLED=0`)

---

## 🚀 Usage

```bash
go build -ldflags="-s -w" -o OFIDO OFIDO.go
./OFIDO --help
./OFIDO --input assertion.json
./OFIDO --input attestation.json --format md
./OFIDO --demo
```

---

## 📦 Part of OwlSec Toolkit

This tool is part of the **OwlSec** suite — a collection of 300+ security and privacy tools.

🔗 [owlsec.org](https://owlsec.org)

---

## ©️ License

MIT License — © Khaled S. Haddad
