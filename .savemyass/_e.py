import os
from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.padding import PKCS7
from cryptography.hazmat.backends import default_backend
import base64

def generate_key(passphrase, salt):
    kdf = PBKDF2HMAC(
        algorithm=hashes.SHA256(),
        length=32,
        salt=salt,
        iterations=100000,
        backend=default_backend()
    )
    return kdf.derive(passphrase.encode())

def encrypt_file(filepath, passphrase):
    with open(filepath, 'rb') as file:
        data = file.read()
    salt = os.urandom(16)
    key = generate_key(passphrase, salt)
    cipher = Cipher(algorithms.AES(key), modes.CBC(salt), backend=default_backend())
    encryptor = cipher.encryptor()
    padder = PKCS7(128).padder()
    padded_data = padder.update(data) + padder.finalize()
    encrypted_data = encryptor.update(padded_data) + encryptor.finalize()
    with open(filepath, 'wb') as file:
        file.write(base64.b64encode(salt + encrypted_data))

def is_base64(data):
    try:
        return base64.b64encode(base64.b64decode(data)) == data
    except:
        return False

def decrypt_file(filepath, passphrase):
    try:
        with open(filepath, 'rb') as file:
            data = file.read()
        
        # Check if file content is base64 encoded (likely encrypted)
        if not is_base64(data):
            print(f"Warning: {filepath} appears to not be encrypted, skipping...")
            return
        
        data = base64.b64decode(data)
        if len(data) < 16:  # Must have at least the salt
            print(f"Warning: {filepath} is too short to be encrypted, skipping...")
            return
            
        salt, encrypted_data = data[:16], data[16:]
        key = generate_key(passphrase, salt)
        cipher = Cipher(algorithms.AES(key), modes.CBC(salt), backend=default_backend())
        decryptor = cipher.decryptor()
        try:
            padded_data = decryptor.update(encrypted_data) + decryptor.finalize()
            unpadder = PKCS7(128).unpadder()
            data = unpadder.update(padded_data) + unpadder.finalize()
            with open(filepath, 'wb') as file:
                file.write(data)
        except ValueError as e:
            print(f"Warning: Failed to decrypt {filepath} - file may not be encrypted or passphrase may be wrong")
            return
        except Exception as e:
            print(f"Warning: Unexpected error decrypting {filepath}: {str(e)}")
            return
    except Exception as e:
        print(f"Warning: Error processing {filepath}: {str(e)}")
        return

if __name__ == "__main__":
    import sys
    if len(sys.argv) != 4:
        print("Usage: python _e.py [encrypt|decrypt] <filepath> <passphrase>")
        sys.exit(1)
    
    command, filepath, passphrase = sys.argv[1:]
    if command == "encrypt":
        encrypt_file(filepath, passphrase)
    elif command == "decrypt":
        decrypt_file(filepath, passphrase)
    else:
        print("Invalid command. Use 'encrypt' or 'decrypt'")
        sys.exit(1)
