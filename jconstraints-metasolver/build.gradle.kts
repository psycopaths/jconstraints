/*
 * Copyright, TU Dortmund, Malte Mues 2021
 */

plugins {
    `java-library`
    `java`
    `maven-publish`
    id("com.github.hierynomus.license") version "0.15.0"
    id("com.github.johnrengelman.shadow") version "5.2.0"
    id("com.github.sherter.google-java-format") version "0.9"
}

repositories {
    jcenter()
    mavenLocal()
}

dependencies {
    testImplementation("org.testng:testng:7.2.0")

    implementation("tools.aqua:jconstraints-all:0.9.6-SNAPSHOT")
}

tasks.test {
    useTestNG() {
        useDefaultListeners = true
        includeGroups = setOf("base")
    }
    testLogging {
        events(
            org.gradle.api.tasks.testing.logging.TestLogEvent.FAILED,
            org.gradle.api.tasks.testing.logging.TestLogEvent.STANDARD_ERROR,
            org.gradle.api.tasks.testing.logging.TestLogEvent.SKIPPED,
            org.gradle.api.tasks.testing.logging.TestLogEvent.PASSED
        )
    }
}


java {
    toolchain {
        languageVersion.set(JavaLanguageVersion.of(8))
    }
}

group = "tools.aqua"
version = "0.9.6-SNAPSHOT"
description = "jConstraints-metasolver"

license {
    header = file("NOTICE")
    excludes(setOf("**/*.smt2", "**/*.txt"))
}

tasks.shadowJar.configure{
    archiveFileName.set("${baseName}-${classifier}-${version}.jar")
}
tasks.shadowJar {
    //FIXME: Exclude the other jconstraints-deps
    exclude("tools.aqua:jconstraints-all:.*")
}

publishing {
    publications {
        create<MavenPublication>("mavenJava") {
            artifactId = "jConstraints-metasolver"
            from(components["java"])
            pom {
                name.set("jConstraints-metasolver")
                description.set("jConstraints-metasolver is the home for solving strategies.")
                url.set("https://github.com/tudo-aqua/jconstraints-metasolver")
                licenses {
                    license {
                        name.set("Apache-2.0")
                        url.set("https://www.apache.org/licenses/LICENSE-2.0.txt")
                    }
                }
                developers {
                    developer {
                        id.set("mmuesly")
                        name.set("Malte Mues")
                        email.set("mail.mues@gmail.com")
                    }
                }
                scm {
                    connection.set("https://github.com/tudo-aqua/jconstraints-metasolver.git")
                    url.set("https://github.com/tudo-aqua/jconstraints-metasolver")
                }
            }
        }
        create<MavenPublication>("publishMaven") {
            artifact(tasks["shadowJar"]){
                classifier = null
            }
            artifactId = "jconstraints--metasolver-all"

        }
    }
}
